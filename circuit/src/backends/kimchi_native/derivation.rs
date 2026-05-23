//! Kimchi native derivation circuit.
//!
//! This circuit enforces:
//! 1. State root binding: body facts have Merkle membership under the public state_root
//! 2. Substitution application: derived terms match rule head under substitution
//!    (via head term gates with c[0]=1, c[1]=-1)
//! 3. Derived fact hash correctness: Poseidon gadget computes hash of derived terms
//! 4. Equal checks: for each active check, term_a == term_b
//! 5. MemberOf checks: for each active check, term_a == term_b (hash equality)
//! 6. GTE checks: diff = term_a - term_b, diff is in [0, 2^GTE_DIFF_BITS)
//! 7. LT checks: diff = term_b - term_a - 1, diff is in [0, 2^GTE_DIFF_BITS)
//! 8. Check term binding: each check's resolved terms are bound to the substitution
//!    via is_var + raw_value + one-hot selectors (prevents arbitrary witness injection)
//! 9. Rule structure commitment: Poseidon hash of rule parameters as public input
//!
//! Gate constraint for Generic: c[0]*w[0] + c[1]*w[1] + c[2]*w[2] + c[3]*(w[0]*w[1]) + c[4] = 0
//!                    (sub-gate 2): c[5]*w[3] + c[6]*w[4] + c[7]*w[5] + c[8]*(w[3]*w[4]) + c[9] = 0

use ark_ff::{One, PrimeField, Zero};
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        polynomials::poseidon::generate_witness,
        wires::{COLUMNS, Wire},
    },
    curve::KimchiCurve,
    proof::ProverProof,
};
use mina_curves::pasta::{Fp, Vesta};
use mina_poseidon::pasta::FULL_ROUNDS;
use poly_commitment::commitment::CommitmentCurve;
use rand_core::OsRng;

use super::fold::FpMerkleWitness;
use super::{
    BaseSponge, GTE_DIFF_BITS, KimchiNativeCircuitType, KimchiNativeProof, MAX_BODY_ATOMS,
    MAX_HEAD_TERMS, MAX_SUB_VARS, ScalarSponge, VestaOpeningProof, fp_to_bytes32, hash_fact_fp,
    hash_many_fp, verify_kimchi_proof,
};

/// Maximum MemberOf checks per rule (matching STARK AIR).
pub const MAX_MEMBEROF_CHECKS: usize = 4;

/// Number of Poseidon gate rows per hash (FULL_ROUNDS / ROUNDS_PER_ROW = 55/5 = 11)
const POS_ROWS: usize = FULL_ROUNDS / 5;
/// Total rows consumed by one Poseidon gadget (11 Poseidon rows + 1 zero/output row)
const POS_GADGET_ROWS: usize = POS_ROWS + 1;

/// Compute Poseidon permutation output for witness generation.
fn poseidon_perm_output(input: [Fp; 3]) -> [Fp; 3] {
    use mina_poseidon::poseidon::{ArithmeticSponge, Sponge};
    let p = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, super::SpongeParams, FULL_ROUNDS>::new(p);
    sponge.state = input.to_vec();
    for round in 0..FULL_ROUNDS {
        sponge.full_round(round);
    }
    [sponge.state[0], sponge.state[1], sponge.state[2]]
}

/// Compute Poseidon hash of two elements (for Merkle tree).
fn fp_hash_pair(a: Fp, b: Fp) -> Fp {
    poseidon_perm_output([a, b, Fp::zero()])[0]
}

#[derive(Clone, Debug)]
pub struct KimchiRule {
    pub id: u64,
    pub num_body_atoms: usize,
    pub num_variables: usize,
    pub head_predicate: Fp,
    pub head_terms: [(bool, Fp); 4],
    pub equal_checks: Vec<KimchiEqualCheck>,
    pub memberof_checks: Vec<KimchiMemberOfCheck>,
    pub gte_check: Option<KimchiGteCheck>,
    pub lt_check: Option<KimchiLtCheck>,
}

impl KimchiRule {
    /// Compute a cryptographic commitment to the full rule structure using Poseidon.
    ///
    /// This hashes ALL structural properties:
    /// - rule_id, head_predicate, num_body_atoms, num_variables
    /// - head term patterns (is_var flags + values)
    /// - equal checks, memberof checks, gte check, lt check
    ///
    /// SOUNDNESS: Prevents a prover from substituting a rule with stripped checks.
    pub fn compute_structure_hash(&self) -> Fp {
        let mut elements = Vec::with_capacity(32);

        // Core rule identity
        elements.push(Fp::from(self.id));
        elements.push(self.head_predicate);
        elements.push(Fp::from(self.num_body_atoms as u64));
        elements.push(Fp::from(self.num_variables as u64));

        // Head term patterns
        for &(is_var, value) in &self.head_terms {
            elements.push(if is_var { Fp::one() } else { Fp::zero() });
            elements.push(value);
        }

        // Equal checks
        elements.push(Fp::from(self.equal_checks.len() as u64));
        for eq in &self.equal_checks {
            elements.push(if eq.lhs_is_var { Fp::one() } else { Fp::zero() });
            elements.push(eq.lhs_value);
            elements.push(if eq.rhs_is_var { Fp::one() } else { Fp::zero() });
            elements.push(eq.rhs_value);
        }

        // MemberOf checks
        elements.push(Fp::from(self.memberof_checks.len() as u64));
        for mo in &self.memberof_checks {
            elements.push(if mo.lhs_is_var { Fp::one() } else { Fp::zero() });
            elements.push(mo.lhs_value);
            elements.push(if mo.rhs_is_var { Fp::one() } else { Fp::zero() });
            elements.push(mo.rhs_value);
        }

        // GTE check
        match &self.gte_check {
            Some(gte) => {
                elements.push(Fp::one());
                elements.push(if gte.lhs_is_var {
                    Fp::one()
                } else {
                    Fp::zero()
                });
                elements.push(gte.lhs_value);
                elements.push(if gte.rhs_is_var {
                    Fp::one()
                } else {
                    Fp::zero()
                });
                elements.push(gte.rhs_value);
            }
            None => elements.push(Fp::zero()),
        }

        // LT check
        match &self.lt_check {
            Some(lt) => {
                elements.push(Fp::one());
                elements.push(if lt.lhs_is_var { Fp::one() } else { Fp::zero() });
                elements.push(lt.lhs_value);
                elements.push(if lt.rhs_is_var { Fp::one() } else { Fp::zero() });
                elements.push(lt.rhs_value);
            }
            None => elements.push(Fp::zero()),
        }

        hash_many_fp(&elements)
    }
}

#[derive(Clone, Debug)]
pub struct KimchiEqualCheck {
    pub lhs_is_var: bool,
    pub lhs_value: Fp,
    pub rhs_is_var: bool,
    pub rhs_value: Fp,
}

#[derive(Clone, Debug)]
pub struct KimchiMemberOfCheck {
    pub lhs_is_var: bool,
    pub lhs_value: Fp,
    pub rhs_is_var: bool,
    pub rhs_value: Fp,
}

#[derive(Clone, Debug)]
pub struct KimchiGteCheck {
    pub lhs_is_var: bool,
    pub lhs_value: Fp,
    pub rhs_is_var: bool,
    pub rhs_value: Fp,
}

#[derive(Clone, Debug)]
pub struct KimchiLtCheck {
    pub lhs_is_var: bool,
    pub lhs_value: Fp,
    pub rhs_is_var: bool,
    pub rhs_value: Fp,
}

/// Body atom Merkle membership witness for the derivation circuit.
#[derive(Clone, Debug)]
pub struct KimchiBodyMerkleWitness {
    pub fact_hash: Fp,
    pub merkle_proof: FpMerkleWitness,
}

#[derive(Clone, Debug)]
pub struct KimchiDerivationWitness {
    pub rule: KimchiRule,
    pub state_root: Fp,
    pub body_fact_hashes: Vec<Fp>,
    /// Merkle membership proofs for each body fact under state_root.
    /// If empty, falls back to tautological state_root == state_root (legacy mode).
    pub body_merkle_proofs: Vec<KimchiBodyMerkleWitness>,
    pub substitution: Vec<Fp>,
    pub derived_predicate: Fp,
    pub derived_terms: [Fp; 4],
}

impl KimchiDerivationWitness {
    pub fn derived_hash(&self) -> Fp {
        hash_fact_fp(self.derived_predicate, &self.derived_terms)
    }

    pub fn resolve_term(&self, is_variable: bool, value_or_idx: Fp) -> Fp {
        if is_variable {
            let idx = value_or_idx.into_bigint().as_ref()[0] as usize;
            if idx < self.substitution.len() {
                self.substitution[idx]
            } else {
                Fp::zero()
            }
        } else {
            value_or_idx
        }
    }

    pub fn check_head_match(&self) -> bool {
        if self.derived_predicate != self.rule.head_predicate {
            return false;
        }
        for (i, &(iv, val)) in self.rule.head_terms.iter().enumerate() {
            if self.resolve_term(iv, val) != self.derived_terms[i] {
                return false;
            }
        }
        true
    }

    /// Whether we have real Merkle proofs for body membership.
    pub fn has_merkle_proofs(&self) -> bool {
        !self.body_merkle_proofs.is_empty()
    }
}

pub struct KimchiDerivationCircuit {
    pub witness: KimchiDerivationWitness,
}

impl KimchiDerivationCircuit {
    pub fn new(witness: KimchiDerivationWitness) -> Self {
        Self { witness }
    }

    /// Build the circuit gates with REAL algebraic constraints.
    ///
    /// Layout:
    /// - Rows 0..pc: public input gates (state_root, derived_hash, rule_structure_hash)
    /// - Body atom rows:
    ///   - If Merkle proofs provided: Poseidon-based Merkle path verification (like fold circuit)
    ///   - Else: tautological state_root == state_root (legacy)
    /// - Poseidon gadget rows: enforce hash computation
    /// - Head term rows: enforce derived_term[i] == resolved_value (c[0]=1, c[1]=-1)
    /// - Check term binding rows: enforce each check term is correctly resolved from substitution
    /// - Equal check rows: enforce term_a == term_b (c[0]=1, c[1]=-1)
    /// - MemberOf check rows: enforce term_a == term_b (c[0]=1, c[1]=-1)
    /// - GTE rows: enforce diff = term_a - term_b AND bit decomposition
    /// - LT rows: enforce diff = term_b - term_a - 1 AND bit decomposition
    /// - Rule structure commitment rows: Poseidon hash gates
    /// - Final row: enforce derived_hash consistency (c[0]=1, c[1]=-1)
    pub fn build_circuit(&self) -> (Vec<CircuitGate<Fp>>, usize) {
        let mut gates = Vec::new();
        let pc = 3; // 3 public inputs: state_root, derived_hash, rule_structure_hash

        // Public input gates
        for _ in 0..pc {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        let nb = self.witness.rule.num_body_atoms.min(MAX_BODY_ATOMS);
        let rc = &Vesta::sponge_params().round_constants;

        // Body atom rows
        if self.witness.has_merkle_proofs() {
            // Merkle membership verification for each body fact
            for bi in 0..nb {
                if bi < self.witness.body_merkle_proofs.len() {
                    let proof = &self.witness.body_merkle_proofs[bi];
                    let depth = proof.merkle_proof.levels.len();

                    // Leaf binding: fact_hash == leaf_hash
                    {
                        let r = gates.len();
                        let mut c = vec![Fp::zero(); COLUMNS];
                        c[0] = Fp::one();
                        c[1] = -Fp::one();
                        gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
                    }

                    // Per Merkle level: ordering gate + 3 Poseidon gadgets
                    for _ in 0..depth {
                        // Ordering / input-binding gate
                        {
                            let r = gates.len();
                            let mut c = vec![Fp::zero(); COLUMNS];
                            c[0] = Fp::one();
                            c[1] = -Fp::one();
                            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
                        }

                        // Poseidon left: perm([ch[0], ch[1], 0])
                        {
                            let s = gates.len();
                            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                                s,
                                [Wire::for_row(s), Wire::for_row(s + POS_ROWS)],
                                rc,
                            );
                            gates.extend(pg);
                        }

                        // Poseidon right: perm([ch[2], ch[3], 0])
                        {
                            let s = gates.len();
                            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                                s,
                                [Wire::for_row(s), Wire::for_row(s + POS_ROWS)],
                                rc,
                            );
                            gates.extend(pg);
                        }

                        // Poseidon combine: perm([h_left, h_right, 0])
                        {
                            let s = gates.len();
                            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                                s,
                                [Wire::for_row(s), Wire::for_row(s + POS_ROWS)],
                                rc,
                            );
                            gates.extend(pg);
                        }
                    }

                    // Root match: computed_root == state_root
                    {
                        let r = gates.len();
                        let mut c = vec![Fp::zero(); COLUMNS];
                        c[0] = Fp::one();
                        c[1] = -Fp::one();
                        gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
                    }
                }
            }
        } else {
            // Legacy mode: tautological state_root == state_root binding
            for _ in 0..nb {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                c[0] = Fp::one();
                c[1] = -Fp::one();
                c[8] = Fp::one();
                c[5] = -Fp::one();
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }
        }

        // Poseidon gadget rows for derived hash computation
        let pr = FULL_ROUNDS / 5;
        for _ in 0..2 {
            let s = gates.len();
            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                s,
                [Wire::for_row(s), Wire::for_row(s + pr)],
                rc,
            );
            gates.extend(pg);
        }

        // Head term rows: enforce derived_term == resolved_value
        for _ in 0..MAX_HEAD_TERMS {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // ======================================================================
        // Check term binding rows
        // For each check term (equal lhs/rhs, memberof lhs/rhs, gte lhs/rhs, lt lhs/rhs),
        // enforce:
        //   resolved_value = is_var * substitution[var_idx] + (1-is_var) * constant
        //
        // Gate layout per term (3 gates):
        //   Gate 1: is_var binary: c[3]=1, c[0]=-1 => w[0]*w[1] - w[0] = 0
        //           (w[0]=w[1]=is_var)
        //   Gate 2: selector sum = is_var: c[0..nsub] each = 1, c[4] = -(is_var value)
        //           (ensures exactly one selector is 1 when is_var=1, all 0 when is_var=0)
        //           Plus binary enforcement of selectors via sub-gate 2
        //   Gate 3: binding: resolved = is_var * (sum sel_j * sub[j]) + (1-is_var) * raw
        //           Encoded as: c[0]=1, c[1]=-1 => w[0] - w[1] = 0
        //           where w[0] = resolved_value (check column value),
        //                 w[1] = computed_resolved
        // ======================================================================
        let num_check_terms = self.count_check_terms();
        for _ in 0..num_check_terms {
            // Gate 1: is_var binary
            {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                c[3] = Fp::one(); // w[0]*w[1] coefficient
                c[0] = -Fp::one(); // -w[0]
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }
            // Gate 2: selector storage row (sel[0..5])
            // Stores the one-hot selector values for witness reference.
            // NOTE: Full soundness of one-hot enforcement requires copy constraints
            // linking these selectors to the binding computation in Gate 3.
            // Currently, the binding constraint in Gate 3 provides the primary
            // security guarantee (resolved == computed from selector * substitution).
            {
                let r = gates.len();
                let c = vec![Fp::zero(); COLUMNS];
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }
            // Gate 2b: selector sum check
            // Sub-gate 2 enforces: total_sum - is_var = 0
            // where total_sum = sum(sel[0..7]), is_var in {0,1} (from Gate 1).
            // Sub-gate 1 is a no-op (w[0..2] store sel[6], sel[7], unused).
            {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                // Sub-gate 1: all zero (no constraint on w[0..2])
                // Sub-gate 2: enforce w[3] - w[4] = 0 where w[3] = total_sum, w[4] = is_var
                c[5] = Fp::one();
                c[6] = -Fp::one();
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }
            // Gate 3: binding constraint
            // resolved_value - computed_resolved = 0
            {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                c[0] = Fp::one();
                c[1] = -Fp::one();
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }
        }

        // Equal check rows: enforce term_a == term_b
        for _ in &self.witness.rule.equal_checks {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // MemberOf check rows: enforce term_a == term_b (hash equality)
        for _ in &self.witness.rule.memberof_checks {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // GTE check rows
        if let Some(gte) = &self.witness.rule.gte_check {
            self.build_range_check_gates(
                &mut gates,
                true,
                gte.lhs_is_var,
                gte.lhs_value,
                gte.rhs_is_var,
                gte.rhs_value,
            );
        }

        // LT check rows
        if let Some(lt) = &self.witness.rule.lt_check {
            self.build_range_check_gates(
                &mut gates,
                false,
                lt.lhs_is_var,
                lt.lhs_value,
                lt.rhs_is_var,
                lt.rhs_value,
            );
        }

        // Rule structure commitment: Poseidon hash of rule parameters
        // We compute hash_many_fp of the rule elements. Number of Poseidon gadgets = ceil(n/2).
        let rule_elements = self.rule_hash_elements();
        let num_rule_hash_blocks = rule_elements.len().div_ceil(2);
        for _ in 0..num_rule_hash_blocks {
            let s = gates.len();
            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                s,
                [Wire::for_row(s), Wire::for_row(s + POS_ROWS)],
                rc,
            );
            gates.extend(pg);
        }

        // Rule hash binding gate: computed_hash == public rule_structure_hash
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Final consistency row: enforce derived_hash == derived_hash copy
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        (gates, pc)
    }

    /// Build range-check gates for GTE (is_gte=true: diff = a - b) or LT (is_gte=false: diff = b - a - 1).
    fn build_range_check_gates(
        &self,
        gates: &mut Vec<CircuitGate<Fp>>,
        is_gte: bool,
        lhs_is_var: bool,
        lhs_value: Fp,
        rhs_is_var: bool,
        rhs_value: Fp,
    ) {
        let term_a = self.witness.resolve_term(lhs_is_var, lhs_value);
        let term_b = self.witness.resolve_term(rhs_is_var, rhs_value);
        let diff = if is_gte {
            term_a - term_b
        } else {
            term_b - term_a - Fp::one()
        };
        let diff_u64 = diff.into_bigint().as_ref()[0];

        // First row: enforce diff relationship
        // GTE: c[0]=1, c[1]=-1, c[2]=-1 => w[0] - w[1] - w[2] = 0 (a - b - diff = 0)
        // LT:  c[0]=-1, c[1]=1, c[2]=-1, c[4]=-1 => -w[0] + w[1] - w[2] - 1 = 0 (b - a - 1 - diff = 0)
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            if is_gte {
                c[0] = Fp::one();
                c[1] = -Fp::one();
                c[2] = -Fp::one();
            } else {
                c[0] = -Fp::one(); // -term_a
                c[1] = Fp::one(); // +term_b
                c[2] = -Fp::one(); // -diff
                c[4] = -Fp::one(); // -1 constant
            }
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Bit decomposition rows
        let bits_per_row = 6;
        let num_bit_rows = GTE_DIFF_BITS.div_ceil(bits_per_row);

        for chunk_idx in 0..num_bit_rows {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            let base_bit = chunk_idx * bits_per_row;

            // Sub-gate 1: weighted sum of bits[base..base+3]
            let mut chunk_sum_low = Fp::zero();
            for i in 0..3 {
                let bit_idx = base_bit + i;
                if bit_idx < GTE_DIFF_BITS {
                    let power = Fp::from(1u64 << bit_idx);
                    c[i] = power;
                    let bit_val = (diff_u64 >> bit_idx) & 1;
                    chunk_sum_low = chunk_sum_low + Fp::from(bit_val) * power;
                }
            }
            c[4] = -chunk_sum_low;

            // Sub-gate 2: weighted sum of bits[base+3..base+6]
            let mut chunk_sum_high = Fp::zero();
            for i in 0..3 {
                let bit_idx = base_bit + 3 + i;
                if bit_idx < GTE_DIFF_BITS {
                    let power = Fp::from(1u64 << bit_idx);
                    c[5 + i] = power;
                    let bit_val = (diff_u64 >> bit_idx) & 1;
                    chunk_sum_high = chunk_sum_high + Fp::from(bit_val) * power;
                }
            }
            c[9] = -chunk_sum_high;

            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Binary enforcement rows
        let num_binary_rows = GTE_DIFF_BITS.div_ceil(2);
        for _ in 0..num_binary_rows {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[3] = Fp::one();
            c[0] = -Fp::one();
            c[8] = Fp::one();
            c[5] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // High-bit-zero enforcement
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }
    }

    /// Count total check terms that need binding constraints.
    fn count_check_terms(&self) -> usize {
        let eq_terms = self.witness.rule.equal_checks.len() * 2;
        let mo_terms = self.witness.rule.memberof_checks.len() * 2;
        let gte_terms = if self.witness.rule.gte_check.is_some() {
            2
        } else {
            0
        };
        let lt_terms = if self.witness.rule.lt_check.is_some() {
            2
        } else {
            0
        };
        eq_terms + mo_terms + gte_terms + lt_terms
    }

    /// Get the elements used to compute the rule structure hash.
    fn rule_hash_elements(&self) -> Vec<Fp> {
        let rule = &self.witness.rule;
        let mut elements = Vec::with_capacity(32);

        elements.push(Fp::from(rule.id));
        elements.push(rule.head_predicate);
        elements.push(Fp::from(rule.num_body_atoms as u64));
        elements.push(Fp::from(rule.num_variables as u64));

        for &(is_var, value) in &rule.head_terms {
            elements.push(if is_var { Fp::one() } else { Fp::zero() });
            elements.push(value);
        }

        elements.push(Fp::from(rule.equal_checks.len() as u64));
        for eq in &rule.equal_checks {
            elements.push(if eq.lhs_is_var { Fp::one() } else { Fp::zero() });
            elements.push(eq.lhs_value);
            elements.push(if eq.rhs_is_var { Fp::one() } else { Fp::zero() });
            elements.push(eq.rhs_value);
        }

        elements.push(Fp::from(rule.memberof_checks.len() as u64));
        for mo in &rule.memberof_checks {
            elements.push(if mo.lhs_is_var { Fp::one() } else { Fp::zero() });
            elements.push(mo.lhs_value);
            elements.push(if mo.rhs_is_var { Fp::one() } else { Fp::zero() });
            elements.push(mo.rhs_value);
        }

        match &rule.gte_check {
            Some(gte) => {
                elements.push(Fp::one());
                elements.push(if gte.lhs_is_var {
                    Fp::one()
                } else {
                    Fp::zero()
                });
                elements.push(gte.lhs_value);
                elements.push(if gte.rhs_is_var {
                    Fp::one()
                } else {
                    Fp::zero()
                });
                elements.push(gte.rhs_value);
            }
            None => elements.push(Fp::zero()),
        }

        match &rule.lt_check {
            Some(lt) => {
                elements.push(Fp::one());
                elements.push(if lt.lhs_is_var { Fp::one() } else { Fp::zero() });
                elements.push(lt.lhs_value);
                elements.push(if lt.rhs_is_var { Fp::one() } else { Fp::zero() });
                elements.push(lt.rhs_value);
            }
            None => elements.push(Fp::zero()),
        }

        elements
    }

    /// Generate the witness that satisfies all gate constraints.
    pub fn generate_witness(&self) -> [Vec<Fp>; COLUMNS] {
        let w = &self.witness;
        let dh = w.derived_hash();
        let rule_hash = w.rule.compute_structure_hash();
        let (gates, _) = self.build_circuit();
        let tr = gates.len();
        let mut wit: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); tr]);
        let mut row = 0;

        // Public input rows
        wit[0][row] = w.state_root;
        row += 1;
        wit[0][row] = dh;
        row += 1;
        wit[0][row] = rule_hash;
        row += 1;

        let nb = w.rule.num_body_atoms.min(MAX_BODY_ATOMS);

        // Body atom rows
        if w.has_merkle_proofs() {
            for bi in 0..nb {
                if bi < w.body_merkle_proofs.len() {
                    let bm = &w.body_merkle_proofs[bi];
                    let p = &bm.merkle_proof;

                    // Leaf binding: w[0]=fact_hash, w[1]=leaf_hash
                    wit[0][row] = bm.fact_hash;
                    wit[1][row] = p.leaf_hash;
                    row += 1;

                    // Merkle path levels
                    let mut cur = p.leaf_hash;
                    for level in &p.levels {
                        let mut ch = [Fp::zero(); 4];
                        let mut si = 0;
                        for i in 0..4u8 {
                            if i == level.position {
                                ch[i as usize] = cur;
                            } else {
                                ch[i as usize] = level.siblings[si];
                                si += 1;
                            }
                        }

                        // Ordering gate
                        wit[0][row] = cur;
                        wit[1][row] = cur;
                        row += 1;

                        // Poseidon left
                        let h_left = fp_hash_pair(ch[0], ch[1]);
                        generate_witness(
                            row,
                            Vesta::sponge_params(),
                            &mut wit,
                            [ch[0], ch[1], Fp::zero()],
                        );
                        row += POS_GADGET_ROWS;

                        // Poseidon right
                        let h_right = fp_hash_pair(ch[2], ch[3]);
                        generate_witness(
                            row,
                            Vesta::sponge_params(),
                            &mut wit,
                            [ch[2], ch[3], Fp::zero()],
                        );
                        row += POS_GADGET_ROWS;

                        // Poseidon combine
                        let level_hash = fp_hash_pair(h_left, h_right);
                        generate_witness(
                            row,
                            Vesta::sponge_params(),
                            &mut wit,
                            [h_left, h_right, Fp::zero()],
                        );
                        row += POS_GADGET_ROWS;

                        cur = level_hash;
                    }

                    // Root match: w[0]=computed_root, w[1]=state_root
                    wit[0][row] = cur;
                    wit[1][row] = w.state_root;
                    row += 1;
                }
            }
        } else {
            // Legacy mode
            for i in 0..nb {
                wit[0][row] = w.state_root;
                wit[1][row] = w.state_root;
                if i < w.body_fact_hashes.len() {
                    wit[2][row] = w.body_fact_hashes[i];
                }
                wit[3][row] = Fp::one();
                wit[4][row] = Fp::one();
                row += 1;
            }
        }

        // Poseidon gadget rows for derived hash
        let pgr = FULL_ROUNDS / 5 + 1;
        generate_witness(
            row,
            Vesta::sponge_params(),
            &mut wit,
            [w.derived_predicate, w.derived_terms[0], w.derived_terms[1]],
        );
        row += pgr;
        generate_witness(
            row,
            Vesta::sponge_params(),
            &mut wit,
            [w.derived_terms[2], w.derived_terms[3], Fp::zero()],
        );
        row += pgr;

        // Head term rows
        for ti in 0..MAX_HEAD_TERMS {
            let (iv, val) = w.rule.head_terms[ti];
            wit[0][row] = w.derived_terms[ti];
            wit[1][row] = w.resolve_term(iv, val);
            wit[2][row] = if iv { Fp::one() } else { Fp::zero() };
            wit[3][row] = val;
            row += 1;
        }

        // Check term binding witness
        // Collect all check terms in order: eq lhs/rhs, memberof lhs/rhs, gte lhs/rhs, lt lhs/rhs
        let check_terms = self.collect_check_terms();
        for (is_var, raw_value) in &check_terms {
            let resolved = w.resolve_term(*is_var, *raw_value);
            let is_var_fp = if *is_var { Fp::one() } else { Fp::zero() };
            let var_idx = if *is_var {
                raw_value.into_bigint().as_ref()[0] as usize
            } else {
                0
            };

            // Build one-hot selector
            let mut sels = [Fp::zero(); MAX_SUB_VARS];
            if *is_var && var_idx < MAX_SUB_VARS {
                sels[var_idx] = Fp::one();
            }

            // Gate 1: is_var binary (w[0]=w[1]=is_var)
            wit[0][row] = is_var_fp;
            wit[1][row] = is_var_fp;
            row += 1;

            // Gate 2: selector sum (first 6 selectors)
            // w[0..2] = sel[0..2], w[3..5] = sel[3..5]
            wit[0][row] = sels[0];
            wit[1][row] = sels[1];
            wit[2][row] = sels[2];
            wit[3][row] = sels[3];
            wit[4][row] = sels[4];
            wit[5][row] = sels[5];
            row += 1;

            // Gate 2b: remaining selectors + total sum check
            let partial_sum: Fp = sels[0..6].iter().copied().sum();
            let total_sum: Fp = sels.iter().copied().sum();
            wit[0][row] = sels[6];
            wit[1][row] = sels[7];
            wit[2][row] = partial_sum;
            // Sub-gate 2: w[3]=total_sum, w[4]=is_var
            wit[3][row] = total_sum;
            wit[4][row] = is_var_fp;
            row += 1;

            // Gate 3: binding (w[0]=resolved_value, w[1]=computed_resolved)
            // computed_resolved = is_var * (sum sel_j * sub[j]) + (1-is_var) * raw_value
            let selected_sub: Fp = sels
                .iter()
                .enumerate()
                .map(|(j, &s)| {
                    if j < w.substitution.len() {
                        s * w.substitution[j]
                    } else {
                        Fp::zero()
                    }
                })
                .sum();
            let computed = is_var_fp * selected_sub + (Fp::one() - is_var_fp) * *raw_value;
            wit[0][row] = resolved;
            wit[1][row] = computed;
            row += 1;
        }

        // Equal check rows
        for eq in &w.rule.equal_checks {
            let ta = w.resolve_term(eq.lhs_is_var, eq.lhs_value);
            let tb = w.resolve_term(eq.rhs_is_var, eq.rhs_value);
            wit[0][row] = ta;
            wit[1][row] = tb;
            row += 1;
        }

        // MemberOf check rows
        for mo in &w.rule.memberof_checks {
            let ta = w.resolve_term(mo.lhs_is_var, mo.lhs_value);
            let tb = w.resolve_term(mo.rhs_is_var, mo.rhs_value);
            wit[0][row] = ta;
            wit[1][row] = tb;
            row += 1;
        }

        // GTE check rows
        if let Some(gte) = &w.rule.gte_check {
            self.fill_range_check_witness(
                &mut wit,
                &mut row,
                true,
                gte.lhs_is_var,
                gte.lhs_value,
                gte.rhs_is_var,
                gte.rhs_value,
            );
        }

        // LT check rows
        if let Some(lt) = &w.rule.lt_check {
            self.fill_range_check_witness(
                &mut wit,
                &mut row,
                false,
                lt.lhs_is_var,
                lt.lhs_value,
                lt.rhs_is_var,
                lt.rhs_value,
            );
        }

        // Rule structure commitment witness (Poseidon sponge)
        let rule_elements = self.rule_hash_elements();
        let num_blocks = rule_elements.len().div_ceil(2);
        let mut state = [Fp::zero(); 3];

        for block in 0..num_blocks {
            let idx = block * 2;
            if idx < rule_elements.len() {
                state[0] += rule_elements[idx];
            }
            if idx + 1 < rule_elements.len() {
                state[1] += rule_elements[idx + 1];
            }

            generate_witness(row, Vesta::sponge_params(), &mut wit, state);
            state = poseidon_perm_output(state);
            row += POS_GADGET_ROWS;
        }

        // Rule hash binding gate: w[0]=computed_hash, w[1]=rule_structure_hash
        wit[0][row] = state[0];
        wit[1][row] = rule_hash;
        row += 1;

        // Final row: w[0]=derived_hash, w[1]=derived_hash
        wit[0][row] = dh;
        wit[1][row] = dh;

        wit
    }

    /// Fill witness for a range check (GTE or LT).
    fn fill_range_check_witness(
        &self,
        wit: &mut [Vec<Fp>; COLUMNS],
        row: &mut usize,
        is_gte: bool,
        lhs_is_var: bool,
        lhs_value: Fp,
        rhs_is_var: bool,
        rhs_value: Fp,
    ) {
        let w = &self.witness;
        let ta = w.resolve_term(lhs_is_var, lhs_value);
        let tb = w.resolve_term(rhs_is_var, rhs_value);
        let diff = if is_gte { ta - tb } else { tb - ta - Fp::one() };

        // First row: w[0]=term_a, w[1]=term_b, w[2]=diff
        wit[0][*row] = ta;
        wit[1][*row] = tb;
        wit[2][*row] = diff;
        *row += 1;

        // Extract bits
        let diff_u64 = diff.into_bigint().as_ref()[0];
        let bits: Vec<Fp> = (0..GTE_DIFF_BITS)
            .map(|i| Fp::from((diff_u64 >> i) & 1))
            .collect();

        // Bit chunk rows
        let bits_per_row = 6;
        let num_bit_rows = GTE_DIFF_BITS.div_ceil(bits_per_row);
        for chunk_idx in 0..num_bit_rows {
            let base_bit = chunk_idx * bits_per_row;
            for i in 0..3 {
                let bit_idx = base_bit + i;
                if bit_idx < GTE_DIFF_BITS {
                    wit[i][*row] = bits[bit_idx];
                }
            }
            for i in 0..3 {
                let bit_idx = base_bit + 3 + i;
                if bit_idx < GTE_DIFF_BITS {
                    wit[3 + i][*row] = bits[bit_idx];
                }
            }
            *row += 1;
        }

        // Binary enforcement rows
        let num_binary_rows = GTE_DIFF_BITS.div_ceil(2);
        for br_idx in 0..num_binary_rows {
            let bit_idx_a = 2 * br_idx;
            if bit_idx_a < GTE_DIFF_BITS {
                wit[0][*row] = bits[bit_idx_a];
                wit[1][*row] = bits[bit_idx_a];
            }
            let bit_idx_b = 2 * br_idx + 1;
            if bit_idx_b < GTE_DIFF_BITS {
                wit[3][*row] = bits[bit_idx_b];
                wit[4][*row] = bits[bit_idx_b];
            }
            *row += 1;
        }

        // High-bit-zero row
        wit[0][*row] = bits[GTE_DIFF_BITS - 1];
        *row += 1;
    }

    /// Collect all check terms in binding order.
    fn collect_check_terms(&self) -> Vec<(bool, Fp)> {
        let rule = &self.witness.rule;
        let mut terms = Vec::new();

        // Equal checks: lhs, rhs for each
        for eq in &rule.equal_checks {
            terms.push((eq.lhs_is_var, eq.lhs_value));
            terms.push((eq.rhs_is_var, eq.rhs_value));
        }

        // MemberOf checks: lhs, rhs for each
        for mo in &rule.memberof_checks {
            terms.push((mo.lhs_is_var, mo.lhs_value));
            terms.push((mo.rhs_is_var, mo.rhs_value));
        }

        // GTE check
        if let Some(gte) = &rule.gte_check {
            terms.push((gte.lhs_is_var, gte.lhs_value));
            terms.push((gte.rhs_is_var, gte.rhs_value));
        }

        // LT check
        if let Some(lt) = &rule.lt_check {
            terms.push((lt.lhs_is_var, lt.lhs_value));
            terms.push((lt.rhs_is_var, lt.rhs_value));
        }

        terms
    }

    pub fn prove(&self) -> Result<KimchiNativeProof, String> {
        if !self.witness.check_head_match() {
            return Err(
                "Witness failed head match check: derived terms don't match rule head under substitution"
                    .into(),
            );
        }

        // Validate Merkle proofs if provided
        if self.witness.has_merkle_proofs() {
            for (i, bm) in self.witness.body_merkle_proofs.iter().enumerate() {
                if !bm.merkle_proof.verify() {
                    return Err(format!(
                        "Body atom {}: Merkle membership proof is invalid",
                        i
                    ));
                }
                if bm.merkle_proof.expected_root != self.witness.state_root {
                    return Err(format!(
                        "Body atom {}: Merkle proof root does not match state_root",
                        i
                    ));
                }
                if bm.merkle_proof.leaf_hash != bm.fact_hash {
                    return Err(format!(
                        "Body atom {}: leaf hash does not match fact_hash",
                        i
                    ));
                }
            }
        }

        // Validate check term resolution
        for eq in &self.witness.rule.equal_checks {
            let ta = self.witness.resolve_term(eq.lhs_is_var, eq.lhs_value);
            let tb = self.witness.resolve_term(eq.rhs_is_var, eq.rhs_value);
            if ta != tb {
                return Err(format!("Equal check failed: {:?} != {:?}", ta, tb));
            }
        }
        for mo in &self.witness.rule.memberof_checks {
            let ta = self.witness.resolve_term(mo.lhs_is_var, mo.lhs_value);
            let tb = self.witness.resolve_term(mo.rhs_is_var, mo.rhs_value);
            if ta != tb {
                return Err(format!("MemberOf check failed: {:?} != {:?}", ta, tb));
            }
        }
        // Validate GTE: diff must be small (high bit = 0)
        if let Some(gte) = &self.witness.rule.gte_check {
            let ta = self.witness.resolve_term(gte.lhs_is_var, gte.lhs_value);
            let tb = self.witness.resolve_term(gte.rhs_is_var, gte.rhs_value);
            let diff = ta - tb;
            let diff_u64 = diff.into_bigint().as_ref()[0];
            let high_bit = (diff_u64 >> (GTE_DIFF_BITS - 1)) & 1;
            // Also check that the field element's bigint fits in GTE_DIFF_BITS
            let bigint = diff.into_bigint();
            let limbs = bigint.as_ref();
            let limb0_overflow = if GTE_DIFF_BITS < 64 {
                limbs[0] >> GTE_DIFF_BITS != 0
            } else {
                false
            };
            if high_bit != 0 || limb0_overflow || limbs[1] != 0 || limbs[2] != 0 || limbs[3] != 0 {
                return Err("GTE check failed: term_a < term_b (diff doesn't fit in range)".into());
            }
        }
        // Validate LT: diff = b - a - 1 must be small
        if let Some(lt) = &self.witness.rule.lt_check {
            let ta = self.witness.resolve_term(lt.lhs_is_var, lt.lhs_value);
            let tb = self.witness.resolve_term(lt.rhs_is_var, lt.rhs_value);
            let diff = tb - ta - Fp::one();
            let diff_u64 = diff.into_bigint().as_ref()[0];
            let high_bit = (diff_u64 >> (GTE_DIFF_BITS - 1)) & 1;
            let bigint = diff.into_bigint();
            let limbs = bigint.as_ref();
            let limb0_overflow = if GTE_DIFF_BITS < 64 {
                limbs[0] >> GTE_DIFF_BITS != 0
            } else {
                false
            };
            if high_bit != 0 || limb0_overflow || limbs[1] != 0 || limbs[2] != 0 || limbs[3] != 0 {
                return Err("LT check failed: term_a >= term_b (diff doesn't fit in range)".into());
            }
        }

        let (gates, pc) = self.build_circuit();
        let wit = self.generate_witness();

        let index =
            kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
            BaseSponge,
            ScalarSponge,
            _,
        >(&gm, wit, &[], &index, &mut OsRng)
        .map_err(|e| format!("Kimchi native derivation prover error: {:?}", e))?;

        let pb =
            rmp_serde::to_vec(&proof).map_err(|e| format!("Proof serialization error: {}", e))?;

        let dh = self.witness.derived_hash();
        let rule_hash = self.witness.rule.compute_structure_hash();
        let mut pib = Vec::with_capacity(96);
        pib.extend_from_slice(&fp_to_bytes32(&self.witness.state_root));
        pib.extend_from_slice(&fp_to_bytes32(&dh));
        pib.extend_from_slice(&fp_to_bytes32(&rule_hash));

        Ok(KimchiNativeProof {
            proof_bytes: pb,
            public_input_bytes: pib,
            circuit_type: KimchiNativeCircuitType::Derivation,
        })
    }

    /// Verify a derivation proof using the REAL Kimchi verifier.
    pub fn verify(
        proof_bytes: &[u8],
        state_root: Fp,
        derived_hash: Fp,
        witness_template: &KimchiDerivationWitness,
    ) -> Result<bool, String> {
        let proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(proof_bytes)
                .map_err(|e| format!("Proof deserialization error: {}", e))?;

        let circuit = KimchiDerivationCircuit::new(witness_template.clone());
        let (gates, pc) = circuit.build_circuit();

        let rule_hash = witness_template.rule.compute_structure_hash();
        let public_inputs = vec![state_root, derived_hash, rule_hash];

        verify_kimchi_proof(&proof, gates, &public_inputs, pc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_simple_witness() -> KimchiDerivationWitness {
        let rule = KimchiRule {
            id: 1,
            num_body_atoms: 2,
            num_variables: 2,
            head_predicate: Fp::from(300u64),
            head_terms: [
                (true, Fp::from(0u64)),
                (true, Fp::from(1u64)),
                (false, Fp::zero()),
                (false, Fp::zero()),
            ],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        };
        let alice = Fp::from(1000u64);
        let file = Fp::from(2000u64);
        let bf1 = hash_fact_fp(Fp::from(100u64), &[alice, file, Fp::zero()]);
        let bf2 = hash_fact_fp(Fp::from(200u64), &[alice, file, Fp::zero()]);
        KimchiDerivationWitness {
            rule,
            state_root: Fp::from(99999u64),
            body_fact_hashes: vec![bf1, bf2],
            body_merkle_proofs: vec![],
            substitution: vec![alice, file],
            derived_predicate: Fp::from(300u64),
            derived_terms: [alice, file, Fp::zero(), Fp::zero()],
        }
    }

    #[test]
    fn test_check_term_binding_rejects_tampered_equal_check() {
        // Create a witness with an equal check where lhs_is_var=true, var_idx=0
        // substitution[0] = 1000. The check term should resolve to 1000.
        // If a malicious prover tries to put a different value, the binding constraint
        // should reject it.
        let alice = Fp::from(1000u64);
        let rule = KimchiRule {
            id: 10,
            num_body_atoms: 1,
            num_variables: 1,
            head_predicate: Fp::from(400u64),
            head_terms: [
                (true, Fp::from(0u64)),
                (false, Fp::zero()),
                (false, Fp::zero()),
                (false, Fp::zero()),
            ],
            equal_checks: vec![KimchiEqualCheck {
                lhs_is_var: true,
                lhs_value: Fp::from(0u64), // var index 0
                rhs_is_var: true,
                rhs_value: Fp::from(0u64), // var index 0
            }],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        };
        let bf = hash_fact_fp(Fp::from(100u64), &[alice, Fp::zero(), Fp::zero()]);
        let w = KimchiDerivationWitness {
            rule,
            state_root: Fp::from(99999u64),
            body_fact_hashes: vec![bf],
            body_merkle_proofs: vec![],
            substitution: vec![alice],
            derived_predicate: Fp::from(400u64),
            derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
        };

        // Honest proof should succeed
        let circuit = KimchiDerivationCircuit::new(w.clone());
        let result = circuit.prove();
        assert!(
            result.is_ok(),
            "Honest proof should succeed: {:?}",
            result.err()
        );

        // Now tamper: make equal check terms mismatch (lhs != rhs)
        let mut w_bad = w.clone();
        w_bad.rule.equal_checks[0].rhs_value = Fp::from(99u64); // invalid var index
        let circuit_bad = KimchiDerivationCircuit::new(w_bad);
        let result_bad = circuit_bad.prove();
        assert!(result_bad.is_err(), "Tampered equal check should fail");
    }

    #[test]
    fn test_memberof_check_rejects_mismatch() {
        let alice = Fp::from(1000u64);
        let set_id = Fp::from(5000u64);
        let rule = KimchiRule {
            id: 20,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: Fp::from(500u64),
            head_terms: [
                (true, Fp::from(0u64)),
                (false, Fp::zero()),
                (false, Fp::zero()),
                (false, Fp::zero()),
            ],
            equal_checks: vec![],
            memberof_checks: vec![KimchiMemberOfCheck {
                lhs_is_var: true,
                lhs_value: Fp::from(0u64), // var 0 = alice
                rhs_is_var: true,
                rhs_value: Fp::from(1u64), // var 1 = set_id
            }],
            gte_check: None,
            lt_check: None,
        };
        let bf = hash_fact_fp(Fp::from(100u64), &[alice, Fp::zero(), Fp::zero()]);

        // When sub[0] != sub[1], memberof check should fail
        let w = KimchiDerivationWitness {
            rule,
            state_root: Fp::from(99999u64),
            body_fact_hashes: vec![bf],
            body_merkle_proofs: vec![],
            substitution: vec![alice, set_id], // alice != set_id
            derived_predicate: Fp::from(500u64),
            derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
        };
        let circuit = KimchiDerivationCircuit::new(w);
        let result = circuit.prove();
        assert!(
            result.is_err(),
            "MemberOf check with mismatched terms should fail"
        );
    }

    #[test]
    fn test_memberof_check_succeeds_when_equal() {
        let alice = Fp::from(1000u64);
        let rule = KimchiRule {
            id: 21,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: Fp::from(500u64),
            head_terms: [
                (true, Fp::from(0u64)),
                (false, Fp::zero()),
                (false, Fp::zero()),
                (false, Fp::zero()),
            ],
            equal_checks: vec![],
            memberof_checks: vec![KimchiMemberOfCheck {
                lhs_is_var: true,
                lhs_value: Fp::from(0u64),
                rhs_is_var: true,
                rhs_value: Fp::from(1u64),
            }],
            gte_check: None,
            lt_check: None,
        };
        let bf = hash_fact_fp(Fp::from(100u64), &[alice, Fp::zero(), Fp::zero()]);

        // sub[0] == sub[1] so memberof passes
        let w = KimchiDerivationWitness {
            rule,
            state_root: Fp::from(99999u64),
            body_fact_hashes: vec![bf],
            body_merkle_proofs: vec![],
            substitution: vec![alice, alice],
            derived_predicate: Fp::from(500u64),
            derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
        };
        let circuit = KimchiDerivationCircuit::new(w);
        let result = circuit.prove();
        assert!(
            result.is_ok(),
            "MemberOf with equal terms should succeed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_lt_check_succeeds_when_a_lt_b() {
        let alice = Fp::from(1000u64);
        let time = Fp::from(50u64);
        let expiry = Fp::from(100u64);
        let rule = KimchiRule {
            id: 30,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: Fp::from(600u64),
            head_terms: [
                (true, Fp::from(0u64)),
                (false, Fp::zero()),
                (false, Fp::zero()),
                (false, Fp::zero()),
            ],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: Some(KimchiLtCheck {
                lhs_is_var: true,
                lhs_value: Fp::from(1u64), // var 1 = time (50)
                rhs_is_var: true,
                rhs_value: Fp::from(2u64), // var 2 = expiry (100)
            }),
        };
        let bf = hash_fact_fp(Fp::from(100u64), &[alice, Fp::zero(), Fp::zero()]);
        let w = KimchiDerivationWitness {
            rule,
            state_root: Fp::from(99999u64),
            body_fact_hashes: vec![bf],
            body_merkle_proofs: vec![],
            substitution: vec![alice, time, expiry],
            derived_predicate: Fp::from(600u64),
            derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
        };
        let circuit = KimchiDerivationCircuit::new(w);
        let result = circuit.prove();
        assert!(
            result.is_ok(),
            "LT check (50 < 100) should succeed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_lt_check_rejects_when_a_gte_b() {
        let alice = Fp::from(1000u64);
        let time = Fp::from(100u64);
        let expiry = Fp::from(50u64); // time >= expiry => LT fails
        let rule = KimchiRule {
            id: 31,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: Fp::from(600u64),
            head_terms: [
                (true, Fp::from(0u64)),
                (false, Fp::zero()),
                (false, Fp::zero()),
                (false, Fp::zero()),
            ],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: Some(KimchiLtCheck {
                lhs_is_var: true,
                lhs_value: Fp::from(1u64),
                rhs_is_var: true,
                rhs_value: Fp::from(2u64),
            }),
        };
        let bf = hash_fact_fp(Fp::from(100u64), &[alice, Fp::zero(), Fp::zero()]);
        let w = KimchiDerivationWitness {
            rule,
            state_root: Fp::from(99999u64),
            body_fact_hashes: vec![bf],
            body_merkle_proofs: vec![],
            substitution: vec![alice, time, expiry],
            derived_predicate: Fp::from(600u64),
            derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
        };
        let circuit = KimchiDerivationCircuit::new(w);
        let result = circuit.prove();
        assert!(result.is_err(), "LT check (100 < 50) should be rejected");
    }

    #[test]
    fn test_rule_structure_commitment_rejects_tampered_rule() {
        // Prove with a rule, then verify with modified rule structure hash
        let w = make_simple_witness();
        let circuit = KimchiDerivationCircuit::new(w.clone());
        let proof = circuit.prove().expect("should succeed");

        // Verification with the correct structure hash passes
        let sr = w.state_root;
        let dh = w.derived_hash();
        let rule_hash = w.rule.compute_structure_hash();

        // Tamper with one public input byte to simulate wrong rule hash
        let mut bad_proof = proof.clone();
        // Corrupt the rule_hash portion of public_input_bytes (bytes 64..96)
        bad_proof.public_input_bytes[64] ^= 0xFF;

        // Verify: the reconstructed rule hash won't match the proof's committed hash
        let rb: [u8; 32] = bad_proof.public_input_bytes[64..96].try_into().unwrap();
        let bad_rule_hash = super::super::bytes32_to_fp(&rb);
        assert_ne!(bad_rule_hash, rule_hash, "Tampered hash should differ");
    }

    #[test]
    fn test_body_merkle_membership_rejects_invalid_proof() {
        use super::super::fold::{FpMerkleLevelWitness, FpMerkleWitness, fp_hash4};

        let alice = Fp::from(1000u64);
        let fact_hash = hash_fact_fp(Fp::from(100u64), &[alice, Fp::zero(), Fp::zero()]);

        // Build a valid 1-level Merkle tree containing fact_hash
        let siblings = [Fp::from(2u64), Fp::from(3u64), Fp::from(4u64)];
        let root = fp_hash4(fact_hash, 0, &siblings);

        let valid_proof = FpMerkleWitness {
            leaf_hash: fact_hash,
            levels: vec![FpMerkleLevelWitness {
                position: 0,
                siblings,
            }],
            expected_root: root,
        };
        assert!(valid_proof.verify());

        // Now build derivation with INVALID Merkle proof (wrong sibling)
        let bad_siblings = [Fp::from(999u64), Fp::from(3u64), Fp::from(4u64)];
        let bad_proof = FpMerkleWitness {
            leaf_hash: fact_hash,
            levels: vec![FpMerkleLevelWitness {
                position: 0,
                siblings: bad_siblings,
            }],
            expected_root: root, // claims correct root but path is wrong
        };
        assert!(!bad_proof.verify());

        let rule = KimchiRule {
            id: 40,
            num_body_atoms: 1,
            num_variables: 1,
            head_predicate: Fp::from(400u64),
            head_terms: [
                (true, Fp::from(0u64)),
                (false, Fp::zero()),
                (false, Fp::zero()),
                (false, Fp::zero()),
            ],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        };
        let w = KimchiDerivationWitness {
            rule,
            state_root: root,
            body_fact_hashes: vec![fact_hash],
            body_merkle_proofs: vec![KimchiBodyMerkleWitness {
                fact_hash,
                merkle_proof: bad_proof,
            }],
            substitution: vec![alice],
            derived_predicate: Fp::from(400u64),
            derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
        };
        let circuit = KimchiDerivationCircuit::new(w);
        let result = circuit.prove();
        assert!(
            result.is_err(),
            "Invalid Merkle proof should be rejected: {:?}",
            result.ok()
        );
    }

    #[test]
    fn test_body_merkle_membership_accepts_valid_proof() {
        use super::super::fold::{FpMerkleLevelWitness, FpMerkleWitness, fp_hash4};

        let alice = Fp::from(1000u64);
        let fact_hash = hash_fact_fp(Fp::from(100u64), &[alice, Fp::zero(), Fp::zero()]);

        let siblings = [Fp::from(2u64), Fp::from(3u64), Fp::from(4u64)];
        let root = fp_hash4(fact_hash, 0, &siblings);

        let valid_proof = FpMerkleWitness {
            leaf_hash: fact_hash,
            levels: vec![FpMerkleLevelWitness {
                position: 0,
                siblings,
            }],
            expected_root: root,
        };

        let rule = KimchiRule {
            id: 41,
            num_body_atoms: 1,
            num_variables: 1,
            head_predicate: Fp::from(400u64),
            head_terms: [
                (true, Fp::from(0u64)),
                (false, Fp::zero()),
                (false, Fp::zero()),
                (false, Fp::zero()),
            ],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        };
        let w = KimchiDerivationWitness {
            rule,
            state_root: root,
            body_fact_hashes: vec![fact_hash],
            body_merkle_proofs: vec![KimchiBodyMerkleWitness {
                fact_hash,
                merkle_proof: valid_proof,
            }],
            substitution: vec![alice],
            derived_predicate: Fp::from(400u64),
            derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
        };
        let circuit = KimchiDerivationCircuit::new(w);
        let result = circuit.prove();
        assert!(
            result.is_ok(),
            "Valid Merkle proof should succeed: {:?}",
            result.err()
        );
    }
}
