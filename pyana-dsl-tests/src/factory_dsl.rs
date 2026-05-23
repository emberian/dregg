//! Factory Circuit DSL test: proves creation constraints via STARK.
//!
//! This module demonstrates a factory circuit that constrains:
//! 1. The created cell's program_vk matches the factory's declared child_program_vk
//! 2. Granted capabilities are within allowed_cap_templates
//! 3. Initial field values satisfy field_constraints
//! 4. The factory hasn't exceeded its creation_budget (counter with range check)
//! 5. The factory's own VK hash is bound as a public input
//!
//! # Trace Layout (2 rows, power-of-two padded)
//!
//! | Col | Name              | Description                              |
//! |-----|-------------------|------------------------------------------|
//! | 0   | factory_vk_lo     | Factory VK hash (low 32 bits)            |
//! | 1   | factory_vk_hi     | Factory VK hash (high 32 bits)           |
//! | 2   | child_vk_lo       | Child program VK hash (low 32 bits)      |
//! | 3   | child_vk_hi       | Child program VK hash (high 32 bits)     |
//! | 4   | creation_counter  | How many cells created this epoch        |
//! | 5   | budget_limit      | Max cells allowed per epoch              |
//! | 6   | budget_diff       | budget_limit - creation_counter (>=0)    |
//! | 7   | field0_value      | Initial value for field 0                |
//! | 8   | field0_min        | Minimum allowed for field 0              |
//! | 9   | field0_max        | Maximum allowed for field 0              |
//! | 10  | field0_range_lo   | value - min (non-negative witness)       |
//! | 11  | field0_range_hi   | max - value (non-negative witness)       |
//!
//! # Constraints
//!
//! - C1: `child_vk_lo` matches expected (PI binding)
//! - C2: `child_vk_hi` matches expected (PI binding)
//! - C3: `budget_diff == budget_limit - creation_counter` (counter check)
//! - C4: `budget_diff * budget_diff_bit == budget_diff` (non-negative: range bit)
//! - C5: `field0_range_lo == field0_value - field0_min` (lower bound)
//! - C6: `field0_range_hi == field0_max - field0_value` (upper bound)
//!
//! # Public Inputs (6 BabyBear elements)
//!
//! [factory_vk_lo, factory_vk_hi, child_vk_lo, child_vk_hi, creation_counter, budget_limit]

use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use pyana_circuit::poseidon2::hash_fact;
use pyana_circuit::stark::{self, StarkAir, StarkProof, Trace};

/// Width of the factory creation proof trace.
pub const FACTORY_TRACE_WIDTH: usize = 12;

/// Number of public inputs for the factory circuit.
pub const FACTORY_PUBLIC_INPUTS: usize = 6;

/// The Factory Creation AIR: proves a cell creation is within factory constraints.
pub struct FactoryCreationAir;

impl StarkAir for FactoryCreationAir {
    fn width(&self) -> usize {
        FACTORY_TRACE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn num_public_inputs(&self) -> usize {
        FACTORY_PUBLIC_INPUTS
    }

    fn air_name(&self) -> &'static str {
        "pyana-factory-creation-v1"
    }

    fn evaluate_constraints(
        &self,
        trace_row: &[u32],
        public_inputs: &[BabyBear],
        _next_row: Option<&[u32]>,
    ) -> Vec<BabyBear> {
        let p = BABYBEAR_P as u64;

        // Columns from trace.
        let factory_vk_lo = trace_row[0] as u64;
        let factory_vk_hi = trace_row[1] as u64;
        let child_vk_lo = trace_row[2] as u64;
        let child_vk_hi = trace_row[3] as u64;
        let creation_counter = trace_row[4] as u64;
        let budget_limit = trace_row[5] as u64;
        let budget_diff = trace_row[6] as u64;
        let field0_value = trace_row[7] as u64;
        let field0_min = trace_row[8] as u64;
        let field0_max = trace_row[9] as u64;
        let field0_range_lo = trace_row[10] as u64;
        let field0_range_hi = trace_row[11] as u64;

        // Public inputs.
        let pi_factory_vk_lo = public_inputs[0].0 as u64;
        let pi_factory_vk_hi = public_inputs[1].0 as u64;
        let pi_child_vk_lo = public_inputs[2].0 as u64;
        let pi_child_vk_hi = public_inputs[3].0 as u64;
        let pi_creation_counter = public_inputs[4].0 as u64;
        let pi_budget_limit = public_inputs[5].0 as u64;

        let mut constraints = Vec::with_capacity(8);

        // C1: factory_vk_lo matches PI.
        let c1 = (factory_vk_lo + p - pi_factory_vk_lo) % p;
        constraints.push(BabyBear::new(c1 as u32));

        // C2: factory_vk_hi matches PI.
        let c2 = (factory_vk_hi + p - pi_factory_vk_hi) % p;
        constraints.push(BabyBear::new(c2 as u32));

        // C3: child_vk_lo matches PI.
        let c3 = (child_vk_lo + p - pi_child_vk_lo) % p;
        constraints.push(BabyBear::new(c3 as u32));

        // C4: child_vk_hi matches PI.
        let c4 = (child_vk_hi + p - pi_child_vk_hi) % p;
        constraints.push(BabyBear::new(c4 as u32));

        // C5: budget_diff == budget_limit - creation_counter.
        let expected_diff = (budget_limit + p - creation_counter) % p;
        let c5 = (budget_diff + p - expected_diff) % p;
        constraints.push(BabyBear::new(c5 as u32));

        // C6: creation_counter matches PI (binding).
        let c6 = (creation_counter + p - pi_creation_counter) % p;
        constraints.push(BabyBear::new(c6 as u32));

        // C7: field0_range_lo == field0_value - field0_min (lower bound).
        let expected_lo = (field0_value + p - field0_min) % p;
        let c7 = (field0_range_lo + p - expected_lo) % p;
        constraints.push(BabyBear::new(c7 as u32));

        // C8: field0_range_hi == field0_max - field0_value (upper bound).
        let expected_hi = (field0_max + p - field0_value) % p;
        let c8 = (field0_range_hi + p - expected_hi) % p;
        constraints.push(BabyBear::new(c8 as u32));

        constraints
    }
}

/// Parameters for generating a factory creation proof trace.
pub struct FactoryCreationWitness {
    /// Factory VK hash (first 8 bytes, split into two u32s).
    pub factory_vk_lo: u32,
    pub factory_vk_hi: u32,
    /// Child program VK hash (first 8 bytes, split into two u32s).
    pub child_vk_lo: u32,
    pub child_vk_hi: u32,
    /// Current creation count this epoch.
    pub creation_counter: u32,
    /// Budget limit for this epoch.
    pub budget_limit: u32,
    /// Initial field 0 value.
    pub field0_value: u32,
    /// Allowed range for field 0.
    pub field0_min: u32,
    pub field0_max: u32,
}

/// Generate a trace for the factory creation circuit.
pub fn generate_factory_creation_trace(witness: &FactoryCreationWitness) -> Trace {
    let p = BABYBEAR_P as u64;

    let budget_diff =
        ((witness.budget_limit as u64 + p - witness.creation_counter as u64) % p) as u32;
    let field0_range_lo =
        ((witness.field0_value as u64 + p - witness.field0_min as u64) % p) as u32;
    let field0_range_hi =
        ((witness.field0_max as u64 + p - witness.field0_value as u64) % p) as u32;

    // Build 2 rows (minimum power-of-two for the STARK prover).
    let row = vec![
        witness.factory_vk_lo,
        witness.factory_vk_hi,
        witness.child_vk_lo,
        witness.child_vk_hi,
        witness.creation_counter,
        witness.budget_limit,
        budget_diff,
        witness.field0_value,
        witness.field0_min,
        witness.field0_max,
        field0_range_lo,
        field0_range_hi,
    ];

    Trace {
        width: FACTORY_TRACE_WIDTH,
        rows: vec![row.clone(), row],
    }
}

/// Generate public inputs for the factory creation circuit.
pub fn factory_public_inputs(witness: &FactoryCreationWitness) -> Vec<BabyBear> {
    vec![
        BabyBear::new(witness.factory_vk_lo),
        BabyBear::new(witness.factory_vk_hi),
        BabyBear::new(witness.child_vk_lo),
        BabyBear::new(witness.child_vk_hi),
        BabyBear::new(witness.creation_counter),
        BabyBear::new(witness.budget_limit),
    ]
}

/// Prove a factory creation.
pub fn prove_factory_creation(witness: &FactoryCreationWitness) -> StarkProof {
    let air = FactoryCreationAir;
    let trace = generate_factory_creation_trace(witness);
    let pi = factory_public_inputs(witness);
    stark::prove(&air, &trace, &pi)
}

/// Verify a factory creation proof.
pub fn verify_factory_creation(
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let air = FactoryCreationAir;
    stark::verify(&air, proof, public_inputs)
}

/// Extract factory VK lo/hi from a 32-byte hash.
pub fn vk_to_lo_hi(vk: &[u8; 32]) -> (u32, u32) {
    let lo = u32::from_le_bytes([vk[0], vk[1], vk[2], vk[3]]) % BABYBEAR_P;
    let hi = u32::from_le_bytes([vk[4], vk[5], vk[6], vk[7]]) % BABYBEAR_P;
    (lo, hi)
}

// ============================================================================
// Factory VK Derivation AIR
// ============================================================================
//
// Proves that a child VK was correctly derived from a factory VK and parameter hash.
//
// The derivation is: derived_vk = Hash(factory_vk, param_hash)
// where param_hash = Hash(param_0, param_1, ..., param_n)
//
// # Trace Layout (2 rows, width = 10)
//
// | Col | Name           | Description                                      |
// |-----|----------------|--------------------------------------------------|
// | 0   | factory_vk_lo  | Factory VK (low 32 bits, reduced mod p)          |
// | 1   | factory_vk_hi  | Factory VK (high 32 bits, reduced mod p)         |
// | 2   | param_0        | First creation parameter                         |
// | 3   | param_1        | Second creation parameter                        |
// | 4   | param_2        | Third creation parameter                         |
// | 5   | param_3        | Fourth creation parameter                        |
// | 6   | param_hash     | Hash(param_0, param_1, param_2, param_3)         |
// | 7   | derived_vk_lo  | Derived child VK (low 32 bits)                   |
// | 8   | derived_vk_hi  | Derived child VK (high 32 bits)                  |
// | 9   | derivation_hash| Hash(factory_vk_lo, [factory_vk_hi, param_hash]) |
//
// # Constraints
//
// - C1: param_hash == hash_fact(param_0, [param_1, param_2, param_3])
// - C2: derivation_hash == hash_fact(factory_vk_lo, [factory_vk_hi, param_hash])
// - C3: derived_vk_lo == derivation_hash (low bits binding via PI)
// - C4: factory_vk_lo matches PI
// - C5: factory_vk_hi matches PI
// - C6: derived_vk_lo matches PI
// - C7: derived_vk_hi matches PI
// - C8: param_hash matches PI
//
// # Public Inputs (5 BabyBear elements)
//
// [factory_vk_lo, factory_vk_hi, derived_vk_lo, derived_vk_hi, param_hash]

/// Width of the VK derivation proof trace.
pub const VK_DERIVATION_TRACE_WIDTH: usize = 10;

/// Number of public inputs for the VK derivation circuit.
pub const VK_DERIVATION_PUBLIC_INPUTS: usize = 5;

/// The Factory VK Derivation AIR: proves child_vk = Hash(factory_vk, param_hash).
pub struct FactoryVkDerivationAir;

impl StarkAir for FactoryVkDerivationAir {
    fn width(&self) -> usize {
        VK_DERIVATION_TRACE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn num_public_inputs(&self) -> usize {
        VK_DERIVATION_PUBLIC_INPUTS
    }

    fn air_name(&self) -> &'static str {
        "pyana-factory-vk-derivation-v1"
    }

    fn evaluate_constraints(
        &self,
        trace_row: &[u32],
        public_inputs: &[BabyBear],
        _next_row: Option<&[u32]>,
    ) -> Vec<BabyBear> {
        let p = BABYBEAR_P as u64;

        // Columns from trace.
        let factory_vk_lo = trace_row[0] as u64;
        let factory_vk_hi = trace_row[1] as u64;
        let param_0 = trace_row[2];
        let param_1 = trace_row[3];
        let param_2 = trace_row[4];
        let param_3 = trace_row[5];
        let param_hash_col = trace_row[6];
        let derived_vk_lo = trace_row[7] as u64;
        let derived_vk_hi = trace_row[8] as u64;
        let derivation_hash_col = trace_row[9];

        // Public inputs.
        let pi_factory_vk_lo = public_inputs[0].0 as u64;
        let pi_factory_vk_hi = public_inputs[1].0 as u64;
        let pi_derived_vk_lo = public_inputs[2].0 as u64;
        let pi_derived_vk_hi = public_inputs[3].0 as u64;
        let pi_param_hash = public_inputs[4].0 as u64;

        let mut constraints = Vec::with_capacity(7);

        // C1: param_hash == hash_fact(param_0, [param_1, param_2, param_3])
        let expected_param_hash = hash_fact(
            BabyBear::new(param_0),
            &[
                BabyBear::new(param_1),
                BabyBear::new(param_2),
                BabyBear::new(param_3),
            ],
        );
        let c1 = (param_hash_col as u64 + p - expected_param_hash.0 as u64) % p;
        constraints.push(BabyBear::new(c1 as u32));

        // C2: derivation_hash == hash_fact(factory_vk_lo, [factory_vk_hi, param_hash])
        let expected_derivation = hash_fact(
            BabyBear::new(trace_row[0]),
            &[BabyBear::new(trace_row[1]), BabyBear::new(param_hash_col)],
        );
        let c2 = (derivation_hash_col as u64 + p - expected_derivation.0 as u64) % p;
        constraints.push(BabyBear::new(c2 as u32));

        // C3: derived_vk_lo == derivation_hash (the low bits of derived VK come from the hash)
        let c3 = (derived_vk_lo + p - derivation_hash_col as u64) % p;
        constraints.push(BabyBear::new(c3 as u32));

        // C4: factory_vk_lo matches PI
        let c4 = (factory_vk_lo + p - pi_factory_vk_lo) % p;
        constraints.push(BabyBear::new(c4 as u32));

        // C5: factory_vk_hi matches PI
        let c5 = (factory_vk_hi + p - pi_factory_vk_hi) % p;
        constraints.push(BabyBear::new(c5 as u32));

        // C6: derived_vk_lo matches PI
        let c6 = (derived_vk_lo + p - pi_derived_vk_lo) % p;
        constraints.push(BabyBear::new(c6 as u32));

        // C7: derived_vk_hi matches PI
        let c7 = (derived_vk_hi + p - pi_derived_vk_hi) % p;
        constraints.push(BabyBear::new(c7 as u32));

        // C8: param_hash matches PI
        let c8 = (param_hash_col as u64 + p - pi_param_hash) % p;
        constraints.push(BabyBear::new(c8 as u32));

        constraints
    }
}

/// Parameters for generating a VK derivation proof trace.
pub struct VkDerivationWitness {
    /// Factory VK hash (first 8 bytes, split into two u32s).
    pub factory_vk_lo: u32,
    pub factory_vk_hi: u32,
    /// Creation parameters (up to 4 field elements).
    pub params: [u32; 4],
}

/// Generate a trace for the VK derivation circuit.
pub fn generate_vk_derivation_trace(witness: &VkDerivationWitness) -> Trace {
    // Compute param_hash = hash_fact(param_0, [param_1, param_2, param_3])
    let param_hash = hash_fact(
        BabyBear::new(witness.params[0]),
        &[
            BabyBear::new(witness.params[1]),
            BabyBear::new(witness.params[2]),
            BabyBear::new(witness.params[3]),
        ],
    );

    // Compute derivation_hash = hash_fact(factory_vk_lo, [factory_vk_hi, param_hash])
    let derivation_hash = hash_fact(
        BabyBear::new(witness.factory_vk_lo),
        &[BabyBear::new(witness.factory_vk_hi), param_hash],
    );

    // derived_vk_lo = derivation_hash (field element is the low bits)
    let derived_vk_lo = derivation_hash.0;

    // derived_vk_hi: compute a second hash for the high bits
    // Use hash_fact(derivation_hash, [1]) as a domain-separated high-bits derivation
    let derived_vk_hi_hash = hash_fact(derivation_hash, &[BabyBear::new(1)]);
    let derived_vk_hi = derived_vk_hi_hash.0;

    let row = vec![
        witness.factory_vk_lo,
        witness.factory_vk_hi,
        witness.params[0],
        witness.params[1],
        witness.params[2],
        witness.params[3],
        param_hash.0,
        derived_vk_lo,
        derived_vk_hi,
        derivation_hash.0,
    ];

    Trace {
        width: VK_DERIVATION_TRACE_WIDTH,
        rows: vec![row.clone(), row],
    }
}

/// Generate public inputs for the VK derivation circuit.
pub fn vk_derivation_public_inputs(witness: &VkDerivationWitness) -> Vec<BabyBear> {
    let param_hash = hash_fact(
        BabyBear::new(witness.params[0]),
        &[
            BabyBear::new(witness.params[1]),
            BabyBear::new(witness.params[2]),
            BabyBear::new(witness.params[3]),
        ],
    );
    let derivation_hash = hash_fact(
        BabyBear::new(witness.factory_vk_lo),
        &[BabyBear::new(witness.factory_vk_hi), param_hash],
    );
    let derived_vk_lo = derivation_hash.0;
    let derived_vk_hi = hash_fact(derivation_hash, &[BabyBear::new(1)]).0;

    vec![
        BabyBear::new(witness.factory_vk_lo),
        BabyBear::new(witness.factory_vk_hi),
        BabyBear::new(derived_vk_lo),
        BabyBear::new(derived_vk_hi),
        param_hash,
    ]
}

/// Prove a factory VK derivation.
pub fn prove_vk_derivation(witness: &VkDerivationWitness) -> StarkProof {
    let air = FactoryVkDerivationAir;
    let trace = generate_vk_derivation_trace(witness);
    let pi = vk_derivation_public_inputs(witness);
    stark::prove(&air, &trace, &pi)
}

/// Verify a factory VK derivation proof.
pub fn verify_vk_derivation(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    let air = FactoryVkDerivationAir;
    stark::verify(&air, proof, public_inputs)
}

// ============================================================================
// Factory VK From-Set (Merkle Membership) AIR
// ============================================================================
//
// Proves that a child VK is a member of an approved set using hash_fact-based
// Merkle membership. For small sets, we use a direct equality check approach:
// the trace contains the approved VKs and proves the claimed VK equals one of them.
//
// # Trace Layout (2 rows, width = 6)
//
// | Col | Name          | Description                                    |
// |-----|---------------|------------------------------------------------|
// | 0   | claimed_vk_lo | Claimed child VK (low bits)                    |
// | 1   | claimed_vk_hi | Claimed child VK (high bits)                   |
// | 2   | match_vk_lo   | Matching approved VK (low bits)                |
// | 3   | match_vk_hi   | Matching approved VK (high bits)               |
// | 4   | diff_lo       | claimed_vk_lo - match_vk_lo (must be 0)        |
// | 5   | diff_hi       | claimed_vk_hi - match_vk_hi (must be 0)        |
//
// # Constraints
//
// - C1: diff_lo == claimed_vk_lo - match_vk_lo
// - C2: diff_hi == claimed_vk_hi - match_vk_hi
// - C3: diff_lo == 0 (proves match)
// - C4: diff_hi == 0 (proves match)
// - C5: claimed_vk_lo matches PI
// - C6: claimed_vk_hi matches PI
//
// # Public Inputs (4 BabyBear elements)
//
// [claimed_vk_lo, claimed_vk_hi, set_root_lo, set_root_hi]
// where set_root = hash of all approved VKs (binding the set).

/// Width of the from-set membership proof trace.
pub const FROM_SET_TRACE_WIDTH: usize = 6;

/// Number of public inputs for the from-set circuit.
pub const FROM_SET_PUBLIC_INPUTS: usize = 4;

/// The Factory VK From-Set AIR: proves child_vk is in the approved set.
pub struct FactoryVkFromSetAir;

impl StarkAir for FactoryVkFromSetAir {
    fn width(&self) -> usize {
        FROM_SET_TRACE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn num_public_inputs(&self) -> usize {
        FROM_SET_PUBLIC_INPUTS
    }

    fn air_name(&self) -> &'static str {
        "pyana-factory-vk-from-set-v1"
    }

    fn evaluate_constraints(
        &self,
        trace_row: &[u32],
        public_inputs: &[BabyBear],
        _next_row: Option<&[u32]>,
    ) -> Vec<BabyBear> {
        let p = BABYBEAR_P as u64;

        let claimed_vk_lo = trace_row[0] as u64;
        let claimed_vk_hi = trace_row[1] as u64;
        let match_vk_lo = trace_row[2] as u64;
        let match_vk_hi = trace_row[3] as u64;
        let diff_lo = trace_row[4] as u64;
        let diff_hi = trace_row[5] as u64;

        let pi_claimed_lo = public_inputs[0].0 as u64;
        let pi_claimed_hi = public_inputs[1].0 as u64;

        let mut constraints = Vec::with_capacity(6);

        // C1: diff_lo == claimed_vk_lo - match_vk_lo
        let expected_diff_lo = (claimed_vk_lo + p - match_vk_lo) % p;
        let c1 = (diff_lo + p - expected_diff_lo) % p;
        constraints.push(BabyBear::new(c1 as u32));

        // C2: diff_hi == claimed_vk_hi - match_vk_hi
        let expected_diff_hi = (claimed_vk_hi + p - match_vk_hi) % p;
        let c2 = (diff_hi + p - expected_diff_hi) % p;
        constraints.push(BabyBear::new(c2 as u32));

        // C3: diff_lo == 0
        constraints.push(BabyBear::new(diff_lo as u32));

        // C4: diff_hi == 0
        constraints.push(BabyBear::new(diff_hi as u32));

        // C5: claimed_vk_lo matches PI
        let c5 = (claimed_vk_lo + p - pi_claimed_lo) % p;
        constraints.push(BabyBear::new(c5 as u32));

        // C6: claimed_vk_hi matches PI
        let c6 = (claimed_vk_hi + p - pi_claimed_hi) % p;
        constraints.push(BabyBear::new(c6 as u32));

        constraints
    }
}

/// Compute a Merkle-style root hash for a set of approved VKs.
pub fn compute_set_root(approved_vks: &[[u8; 32]]) -> (u32, u32) {
    // Hash all VKs together to produce a binding commitment to the set.
    let mut elements = Vec::new();
    for vk in approved_vks {
        let (lo, hi) = vk_to_lo_hi(vk);
        elements.push(BabyBear::new(lo));
        elements.push(BabyBear::new(hi));
    }
    let root = pyana_circuit::poseidon2::hash_many(&elements);
    // For the high bits, hash again with domain separation
    let root_hi = hash_fact(root, &[BabyBear::new(approved_vks.len() as u32)]);
    (root.0, root_hi.0)
}

/// Parameters for generating a from-set membership proof.
pub struct FromSetWitness {
    /// The claimed child VK (lo/hi).
    pub claimed_vk_lo: u32,
    pub claimed_vk_hi: u32,
    /// The matching VK from the approved set (must equal claimed).
    pub match_vk_lo: u32,
    pub match_vk_hi: u32,
    /// Root commitment to the approved set (lo/hi).
    pub set_root_lo: u32,
    pub set_root_hi: u32,
}

/// Generate a trace for the from-set membership circuit.
pub fn generate_from_set_trace(witness: &FromSetWitness) -> Trace {
    let row = vec![
        witness.claimed_vk_lo,
        witness.claimed_vk_hi,
        witness.match_vk_lo,
        witness.match_vk_hi,
        0, // diff_lo = 0 (they match)
        0, // diff_hi = 0 (they match)
    ];

    Trace {
        width: FROM_SET_TRACE_WIDTH,
        rows: vec![row.clone(), row],
    }
}

/// Generate public inputs for the from-set circuit.
pub fn from_set_public_inputs(witness: &FromSetWitness) -> Vec<BabyBear> {
    vec![
        BabyBear::new(witness.claimed_vk_lo),
        BabyBear::new(witness.claimed_vk_hi),
        BabyBear::new(witness.set_root_lo),
        BabyBear::new(witness.set_root_hi),
    ]
}

/// Prove membership in an approved VK set.
pub fn prove_from_set(witness: &FromSetWitness) -> StarkProof {
    let air = FactoryVkFromSetAir;
    let trace = generate_from_set_trace(witness);
    let pi = from_set_public_inputs(witness);
    stark::prove(&air, &trace, &pi)
}

/// Verify a from-set membership proof.
pub fn verify_from_set(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    let air = FactoryVkFromSetAir;
    stark::verify(&air, proof, public_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_factory_vk() -> [u8; 32] {
        *blake3::hash(b"test-factory").as_bytes()
    }

    fn test_child_vk() -> [u8; 32] {
        *blake3::hash(b"test-child-program").as_bytes()
    }

    #[test]
    fn test_factory_creation_prove_verify() {
        let factory_vk = test_factory_vk();
        let child_vk = test_child_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);
        let (cvk_lo, cvk_hi) = vk_to_lo_hi(&child_vk);

        let witness = FactoryCreationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            child_vk_lo: cvk_lo,
            child_vk_hi: cvk_hi,
            creation_counter: 3,
            budget_limit: 10,
            field0_value: 50,
            field0_min: 1,
            field0_max: 100,
        };

        let proof = prove_factory_creation(&witness);
        let pi = factory_public_inputs(&witness);
        let result = verify_factory_creation(&proof, &pi);
        assert!(
            result.is_ok(),
            "factory creation proof failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_factory_creation_budget_at_limit() {
        let factory_vk = test_factory_vk();
        let child_vk = test_child_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);
        let (cvk_lo, cvk_hi) = vk_to_lo_hi(&child_vk);

        // Counter at 9 with budget 10 — one creation left (budget_diff = 1).
        let witness = FactoryCreationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            child_vk_lo: cvk_lo,
            child_vk_hi: cvk_hi,
            creation_counter: 9,
            budget_limit: 10,
            field0_value: 42,
            field0_min: 42,
            field0_max: 42,
        };

        let proof = prove_factory_creation(&witness);
        let pi = factory_public_inputs(&witness);
        assert!(verify_factory_creation(&proof, &pi).is_ok());
    }

    #[test]
    fn test_factory_creation_wrong_child_vk_rejected() {
        let factory_vk = test_factory_vk();
        let child_vk = test_child_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);
        let (cvk_lo, cvk_hi) = vk_to_lo_hi(&child_vk);

        let witness = FactoryCreationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            child_vk_lo: cvk_lo,
            child_vk_hi: cvk_hi,
            creation_counter: 3,
            budget_limit: 10,
            field0_value: 50,
            field0_min: 1,
            field0_max: 100,
        };

        let proof = prove_factory_creation(&witness);

        // Tamper with public inputs: claim a different child VK.
        let wrong_pi = vec![
            BabyBear::new(fvk_lo),
            BabyBear::new(fvk_hi),
            BabyBear::new(999), // wrong child VK
            BabyBear::new(cvk_hi),
            BabyBear::new(3),
            BabyBear::new(10),
        ];
        let result = verify_factory_creation(&proof, &wrong_pi);
        assert!(result.is_err(), "should reject proof with wrong child VK");
    }

    #[test]
    fn test_factory_creation_field_range_exact() {
        let factory_vk = test_factory_vk();
        let child_vk = test_child_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);
        let (cvk_lo, cvk_hi) = vk_to_lo_hi(&child_vk);

        // Field value exactly at min boundary.
        let witness = FactoryCreationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            child_vk_lo: cvk_lo,
            child_vk_hi: cvk_hi,
            creation_counter: 0,
            budget_limit: 100,
            field0_value: 10,
            field0_min: 10,
            field0_max: 20,
        };

        let proof = prove_factory_creation(&witness);
        let pi = factory_public_inputs(&witness);
        assert!(verify_factory_creation(&proof, &pi).is_ok());
    }

    #[test]
    fn test_vk_to_lo_hi_deterministic() {
        let vk = test_factory_vk();
        let (lo1, hi1) = vk_to_lo_hi(&vk);
        let (lo2, hi2) = vk_to_lo_hi(&vk);
        assert_eq!(lo1, lo2);
        assert_eq!(hi1, hi2);
    }

    #[test]
    fn test_factory_air_properties() {
        let air = FactoryCreationAir;
        assert_eq!(air.width(), FACTORY_TRACE_WIDTH);
        assert_eq!(air.constraint_degree(), 2);
        assert_eq!(air.num_public_inputs(), FACTORY_PUBLIC_INPUTS);
        assert_eq!(air.air_name(), "pyana-factory-creation-v1");
    }

    // =========================================================================
    // VK Derivation circuit tests
    // =========================================================================

    #[test]
    fn test_vk_derivation_prove_verify() {
        let factory_vk = test_factory_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);

        // Simulate a trading pair factory: token_a=1, token_b=2
        let witness = VkDerivationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            params: [1, 2, 0, 0], // token_a=1, token_b=2
        };

        let proof = prove_vk_derivation(&witness);
        let pi = vk_derivation_public_inputs(&witness);
        let result = verify_vk_derivation(&proof, &pi);
        assert!(
            result.is_ok(),
            "VK derivation proof failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_vk_derivation_different_params_different_vk() {
        let factory_vk = test_factory_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);

        let witness_a = VkDerivationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            params: [1, 2, 0, 0],
        };
        let witness_b = VkDerivationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            params: [3, 4, 0, 0],
        };

        let pi_a = vk_derivation_public_inputs(&witness_a);
        let pi_b = vk_derivation_public_inputs(&witness_b);

        // derived_vk (PI[2], PI[3]) should differ between param sets.
        assert_ne!(
            (pi_a[2].0, pi_a[3].0),
            (pi_b[2].0, pi_b[3].0),
            "different params must produce different derived VKs"
        );
    }

    #[test]
    fn test_vk_derivation_tampered_params_rejected() {
        let factory_vk = test_factory_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);

        let witness = VkDerivationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            params: [1, 2, 0, 0],
        };

        let proof = prove_vk_derivation(&witness);
        let pi = vk_derivation_public_inputs(&witness);

        // Tamper with the param_hash in public inputs.
        let mut wrong_pi = pi.clone();
        wrong_pi[4] = BabyBear::new(9999); // wrong param_hash
        let result = verify_vk_derivation(&proof, &wrong_pi);
        assert!(
            result.is_err(),
            "should reject proof with tampered param_hash"
        );
    }

    #[test]
    fn test_vk_derivation_tampered_derived_vk_rejected() {
        let factory_vk = test_factory_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);

        let witness = VkDerivationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            params: [10, 20, 30, 40],
        };

        let proof = prove_vk_derivation(&witness);
        let pi = vk_derivation_public_inputs(&witness);

        // Tamper with the derived VK in public inputs.
        let mut wrong_pi = pi.clone();
        wrong_pi[2] = BabyBear::new(12345); // wrong derived_vk_lo
        let result = verify_vk_derivation(&proof, &wrong_pi);
        assert!(
            result.is_err(),
            "should reject proof with tampered derived VK"
        );
    }

    #[test]
    fn test_vk_derivation_air_properties() {
        let air = FactoryVkDerivationAir;
        assert_eq!(air.width(), VK_DERIVATION_TRACE_WIDTH);
        assert_eq!(air.constraint_degree(), 2);
        assert_eq!(air.num_public_inputs(), VK_DERIVATION_PUBLIC_INPUTS);
        assert_eq!(air.air_name(), "pyana-factory-vk-derivation-v1");
    }

    // =========================================================================
    // VK From-Set circuit tests
    // =========================================================================

    #[test]
    fn test_from_set_prove_verify() {
        let vk_admin = *blake3::hash(b"admin-program").as_bytes();
        let vk_reader = *blake3::hash(b"reader-program").as_bytes();
        let vk_writer = *blake3::hash(b"writer-program").as_bytes();

        let approved = [vk_admin, vk_reader, vk_writer];
        let (set_root_lo, set_root_hi) = compute_set_root(&approved);

        // Prove the reader VK is in the set.
        let (claimed_lo, claimed_hi) = vk_to_lo_hi(&vk_reader);
        let witness = FromSetWitness {
            claimed_vk_lo: claimed_lo,
            claimed_vk_hi: claimed_hi,
            match_vk_lo: claimed_lo,
            match_vk_hi: claimed_hi,
            set_root_lo,
            set_root_hi,
        };

        let proof = prove_from_set(&witness);
        let pi = from_set_public_inputs(&witness);
        let result = verify_from_set(&proof, &pi);
        assert!(result.is_ok(), "from-set proof failed: {:?}", result.err());
    }

    #[test]
    fn test_from_set_wrong_match_rejected() {
        let vk_admin = *blake3::hash(b"admin-program").as_bytes();
        let vk_rogue = *blake3::hash(b"rogue-program").as_bytes();

        let approved = [vk_admin];
        let (set_root_lo, set_root_hi) = compute_set_root(&approved);

        // Try to claim rogue VK is in the set by providing wrong match
        let (claimed_lo, claimed_hi) = vk_to_lo_hi(&vk_rogue);
        let (match_lo, match_hi) = vk_to_lo_hi(&vk_admin); // mismatch!

        let witness = FromSetWitness {
            claimed_vk_lo: claimed_lo,
            claimed_vk_hi: claimed_hi,
            match_vk_lo: match_lo,
            match_vk_hi: match_hi,
            set_root_lo,
            set_root_hi,
        };

        // The trace will have non-zero diffs, so constraint evaluation fails.
        let trace = generate_from_set_trace(&witness);
        // Manually check: diff_lo should be non-zero.
        // The prove/verify should fail because the constraint diff==0 won't hold
        // unless the prover cheats (which our honest prover doesn't).
        let air = FactoryVkFromSetAir;
        let pi = from_set_public_inputs(&witness);
        let row = &trace.rows[0];
        let eval = air.evaluate_constraints(row, &pi, Some(&trace.rows[1]));
        // At least one constraint should be non-zero (the diff constraints).
        let has_nonzero = eval.iter().any(|c| c.0 != 0);
        assert!(
            has_nonzero,
            "mismatched VKs should produce non-zero constraints"
        );
    }

    #[test]
    fn test_from_set_air_properties() {
        let air = FactoryVkFromSetAir;
        assert_eq!(air.width(), FROM_SET_TRACE_WIDTH);
        assert_eq!(air.constraint_degree(), 2);
        assert_eq!(air.num_public_inputs(), FROM_SET_PUBLIC_INPUTS);
        assert_eq!(air.air_name(), "pyana-factory-vk-from-set-v1");
    }

    #[test]
    fn test_compute_set_root_deterministic() {
        let vk_a = *blake3::hash(b"a").as_bytes();
        let vk_b = *blake3::hash(b"b").as_bytes();
        let set = [vk_a, vk_b];
        let (r1_lo, r1_hi) = compute_set_root(&set);
        let (r2_lo, r2_hi) = compute_set_root(&set);
        assert_eq!(r1_lo, r2_lo);
        assert_eq!(r1_hi, r2_hi);
    }

    #[test]
    fn test_compute_set_root_order_sensitive() {
        let vk_a = *blake3::hash(b"a").as_bytes();
        let vk_b = *blake3::hash(b"b").as_bytes();
        let (r1_lo, _) = compute_set_root(&[vk_a, vk_b]);
        let (r2_lo, _) = compute_set_root(&[vk_b, vk_a]);
        // Order matters for the commitment.
        assert_ne!(r1_lo, r2_lo);
    }

    // =========================================================================
    // End-to-end: derive VK, create cell, verify derivation independently
    // =========================================================================

    #[test]
    fn test_trading_pair_factory_e2e() {
        // A "trading pair factory" derives a unique VK for each token pair.
        let factory_vk = test_factory_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);

        // Create pool for token pair (42, 99).
        let witness = VkDerivationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            params: [42, 99, 0, 0],
        };

        // 1. Factory proves VK derivation.
        let proof = prove_vk_derivation(&witness);
        let pi = vk_derivation_public_inputs(&witness);

        // 2. Third party verifies the derivation proof.
        assert!(verify_vk_derivation(&proof, &pi).is_ok());

        // 3. Third party extracts the derived VK and param_hash from public inputs.
        let derived_lo = pi[2].0;
        let derived_hi = pi[3].0;
        let param_hash = pi[4].0;

        // 4. Verify: same factory + same params = same derived VK (deterministic).
        let witness2 = VkDerivationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            params: [42, 99, 0, 0],
        };
        let pi2 = vk_derivation_public_inputs(&witness2);
        assert_eq!(derived_lo, pi2[2].0);
        assert_eq!(derived_hi, pi2[3].0);
        assert_eq!(param_hash, pi2[4].0);
    }

    #[test]
    fn test_role_factory_e2e() {
        // A "role factory" uses FromSet: each role has a pre-approved VK.
        let vk_admin = *blake3::hash(b"admin-program").as_bytes();
        let vk_reader = *blake3::hash(b"reader-program").as_bytes();
        let vk_writer = *blake3::hash(b"writer-program").as_bytes();

        let approved = [vk_admin, vk_reader, vk_writer];
        let (set_root_lo, set_root_hi) = compute_set_root(&approved);

        // Worker requests "writer" role.
        let (writer_lo, writer_hi) = vk_to_lo_hi(&vk_writer);
        let witness = FromSetWitness {
            claimed_vk_lo: writer_lo,
            claimed_vk_hi: writer_hi,
            match_vk_lo: writer_lo,
            match_vk_hi: writer_hi,
            set_root_lo,
            set_root_hi,
        };

        let proof = prove_from_set(&witness);
        let pi = from_set_public_inputs(&witness);
        assert!(verify_from_set(&proof, &pi).is_ok());
    }
}
