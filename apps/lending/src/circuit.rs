//! Circuit descriptors for lending protocol proofs.
//!
//! Two main circuits:
//! - HealthFactorCircuit: proves collateral_value * threshold >= debt_value * BPS_SCALE
//! - InterestAccrualCircuit: proves correct compound interest computation
//!
//! These use pyana-circuit's DSL/STARK infrastructure to produce cryptographic proofs
//! that can be verified without access to the underlying position data.

use std::collections::HashMap;

use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use pyana_dsl_runtime::{
    BoundaryDef, BoundaryRow, CellProgram, CircuitDescriptor, ColumnDef, ColumnKind,
    ConstraintExpr, PolyTerm, ProgramRegistry,
};
use serde::{Deserialize, Serialize};

use crate::interest::BPS_SCALE;

// =============================================================================
// Health Factor Circuit
// =============================================================================

/// Trace width for the health factor circuit.
///
/// Layout (single row):
/// | 0  | collateral_value (sum of amount*price for all collateral) |
/// | 1  | debt_amount                                                |
/// | 2  | threshold_bps                                              |
/// | 3  | lhs = collateral_value * threshold_bps                    |
/// | 4  | rhs = debt_amount * BPS_SCALE                              |
/// | 5  | diff = lhs - rhs (must be >= 0)                           |
/// | 6  | diff_high_bit (0 if diff < p/2 -- non-negative)           |
pub const HEALTH_FACTOR_WIDTH: usize = 7;

/// Number of public inputs for the health factor circuit.
pub const HEALTH_FACTOR_PI_COUNT: usize = 3;

/// Column indices for health factor circuit.
pub mod health_col {
    pub const COLLATERAL_VALUE: usize = 0;
    pub const DEBT_AMOUNT: usize = 1;
    pub const THRESHOLD_BPS: usize = 2;
    pub const LHS: usize = 3;
    pub const RHS: usize = 4;
    pub const DIFF: usize = 5;
    pub const DIFF_HIGH_BIT: usize = 6;
}

/// Public input indices for health factor circuit.
pub mod health_pi {
    pub const COLLATERAL_VALUE: usize = 0;
    pub const DEBT_AMOUNT: usize = 1;
    pub const THRESHOLD_BPS: usize = 2;
}

/// Build the health factor circuit descriptor.
///
/// This circuit proves that a lending position is solvent:
/// `collateral_value * threshold_bps >= debt_amount * BPS_SCALE`
///
/// The proof is achieved by computing `diff = lhs - rhs` and showing `diff` is
/// non-negative (high bit is zero in BabyBear field representation).
pub fn health_factor_circuit_descriptor() -> CircuitDescriptor {
    CircuitDescriptor {
        name: "pyana-lending-health-factor-v1".to_string(),
        trace_width: HEALTH_FACTOR_WIDTH,
        max_degree: 2,
        columns: vec![
            ColumnDef {
                name: "collateral_value".into(),
                index: health_col::COLLATERAL_VALUE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "debt_amount".into(),
                index: health_col::DEBT_AMOUNT,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "threshold_bps".into(),
                index: health_col::THRESHOLD_BPS,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "lhs".into(),
                index: health_col::LHS,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "rhs".into(),
                index: health_col::RHS,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "diff".into(),
                index: health_col::DIFF,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "diff_high_bit".into(),
                index: health_col::DIFF_HIGH_BIT,
                kind: ColumnKind::Binary,
            },
        ],
        constraints: vec![
            // C1: lhs == collateral_value * threshold_bps
            ConstraintExpr::Multiplication {
                a: health_col::COLLATERAL_VALUE,
                b: health_col::THRESHOLD_BPS,
                output: health_col::LHS,
            },
            // C2: rhs == debt_amount * BPS_SCALE
            // rhs - debt_amount * BPS_SCALE == 0
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![health_col::RHS],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - BPS_SCALE as u32),
                        col_indices: vec![health_col::DEBT_AMOUNT],
                    },
                ],
            },
            // C3: diff == lhs - rhs
            // diff - lhs + rhs == 0
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![health_col::DIFF],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![health_col::LHS],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![health_col::RHS],
                    },
                ],
            },
            // C4: diff_high_bit is boolean
            ConstraintExpr::Binary {
                col: health_col::DIFF_HIGH_BIT,
            },
            // C5: diff_high_bit == 0 (enforces diff is non-negative, i.e. < p/2)
            ConstraintExpr::Polynomial {
                terms: vec![PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![health_col::DIFF_HIGH_BIT],
                }],
            },
            // C6-C8: Public input bindings
            ConstraintExpr::PiBinding {
                col: health_col::COLLATERAL_VALUE,
                pi_index: health_pi::COLLATERAL_VALUE,
            },
            ConstraintExpr::PiBinding {
                col: health_col::DEBT_AMOUNT,
                pi_index: health_pi::DEBT_AMOUNT,
            },
            ConstraintExpr::PiBinding {
                col: health_col::THRESHOLD_BPS,
                pi_index: health_pi::THRESHOLD_BPS,
            },
        ],
        boundaries: vec![
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: health_col::COLLATERAL_VALUE,
                pi_index: health_pi::COLLATERAL_VALUE,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: health_col::DEBT_AMOUNT,
                pi_index: health_pi::DEBT_AMOUNT,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: health_col::THRESHOLD_BPS,
                pi_index: health_pi::THRESHOLD_BPS,
            },
        ],
        public_input_count: HEALTH_FACTOR_PI_COUNT,
    }
}

/// Create a CellProgram for the health factor circuit.
pub fn health_factor_cell_program() -> CellProgram {
    CellProgram::new(health_factor_circuit_descriptor(), 1)
}

/// Deploy the health factor circuit to a ProgramRegistry. Returns the VK hash.
pub fn deploy_health_factor_program(
    registry: &mut ProgramRegistry,
) -> Result<[u8; 32], pyana_dsl_runtime::ProgramError> {
    let program = health_factor_cell_program();
    registry.deploy(program)
}

// =============================================================================
// Interest Accrual Circuit
// =============================================================================

/// Trace width for the interest accrual circuit.
///
/// Layout (per block row):
/// | 0  | block_index (0..N-1)                |
/// | 1  | balance (current balance at step)    |
/// | 2  | rate_per_block (fixed for period)    |
/// | 3  | interest_this_block                  |
/// | 4  | next_balance (balance + interest)    |
pub const INTEREST_ACCRUAL_WIDTH: usize = 5;

/// Number of public inputs for the interest accrual circuit.
pub const INTEREST_ACCRUAL_PI_COUNT: usize = 4;

/// Column indices for interest accrual circuit.
pub mod accrual_col {
    pub const BLOCK_INDEX: usize = 0;
    pub const BALANCE: usize = 1;
    pub const RATE: usize = 2;
    pub const INTEREST: usize = 3;
    pub const NEXT_BALANCE: usize = 4;
}

/// Public input indices for interest accrual circuit.
pub mod accrual_pi {
    pub const START_BALANCE: usize = 0;
    pub const END_BALANCE: usize = 1;
    pub const RATE: usize = 2;
    pub const NUM_BLOCKS: usize = 3;
}

/// Precision for per-block rate (rate is expressed as numerator with this denominator).
pub const RATE_PRECISION: u64 = 1_000_000_000;

/// Build the interest accrual circuit descriptor.
///
/// This circuit proves correct compound interest computation:
/// `new_balance = old_balance * (1 + rate)^num_blocks`
/// realized as iterated multiplication: each row computes one block of interest.
///
/// Constraints:
/// 1. next_balance == balance + interest
/// 2. Transition: balance[i+1] == next_balance[i]
/// 3. Block index increments
/// 4. Public input bindings (start_balance at first row, end_balance at last row)
pub fn interest_accrual_circuit_descriptor() -> CircuitDescriptor {
    CircuitDescriptor {
        name: "pyana-lending-interest-accrual-v1".to_string(),
        trace_width: INTEREST_ACCRUAL_WIDTH,
        max_degree: 2,
        columns: vec![
            ColumnDef {
                name: "block_index".into(),
                index: accrual_col::BLOCK_INDEX,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "balance".into(),
                index: accrual_col::BALANCE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "rate".into(),
                index: accrual_col::RATE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "interest".into(),
                index: accrual_col::INTEREST,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "next_balance".into(),
                index: accrual_col::NEXT_BALANCE,
                kind: ColumnKind::Value,
            },
        ],
        constraints: vec![
            // C1: next_balance == balance + interest
            // next_balance - balance - interest == 0
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![accrual_col::NEXT_BALANCE],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![accrual_col::BALANCE],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![accrual_col::INTEREST],
                    },
                ],
            },
            // C2: Transition: next row's balance == this row's next_balance
            ConstraintExpr::Transition {
                next_col: accrual_col::BALANCE,
                local_col: accrual_col::NEXT_BALANCE,
            },
            // C3: Public input binding: rate is constant across all rows
            ConstraintExpr::PiBinding {
                col: accrual_col::RATE,
                pi_index: accrual_pi::RATE,
            },
        ],
        boundaries: vec![
            // First row: balance == start_balance (PI[0])
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: accrual_col::BALANCE,
                pi_index: accrual_pi::START_BALANCE,
            },
            // Last row: next_balance == end_balance (PI[1])
            BoundaryDef::PiBinding {
                row: BoundaryRow::Last,
                col: accrual_col::NEXT_BALANCE,
                pi_index: accrual_pi::END_BALANCE,
            },
            // First row: rate bound to PI[2]
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: accrual_col::RATE,
                pi_index: accrual_pi::RATE,
            },
            // First row: block_index starts at 0
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: accrual_col::BLOCK_INDEX,
                value: BabyBear::ZERO,
            },
        ],
        public_input_count: INTEREST_ACCRUAL_PI_COUNT,
    }
}

/// Create a CellProgram for the interest accrual circuit.
pub fn interest_accrual_cell_program() -> CellProgram {
    CellProgram::new(interest_accrual_circuit_descriptor(), 1)
}

/// Deploy the interest accrual circuit to a ProgramRegistry. Returns the VK hash.
pub fn deploy_interest_accrual_program(
    registry: &mut ProgramRegistry,
) -> Result<[u8; 32], pyana_dsl_runtime::ProgramError> {
    let program = interest_accrual_cell_program();
    registry.deploy(program)
}

// =============================================================================
// Witness types
// =============================================================================

/// Scale factor: we divide large values by this to fit in BabyBear range.
/// BabyBear p ~ 2^31, so values up to ~2B are safe. We scale by 1000 to give
/// comfortable headroom for multiplications.
const SCALE_FACTOR: u64 = 1000;

/// Witness for the health factor circuit.
#[derive(Clone, Debug)]
pub struct HealthFactorWitness {
    /// Collateral amounts per asset.
    pub collateral_amounts: Vec<u64>,
    /// Collateral prices per asset (must match amounts length).
    pub collateral_prices: Vec<u64>,
    /// Total debt value.
    pub debt_amount: u64,
    /// Liquidation threshold in basis points.
    pub threshold_bps: u64,
}

impl HealthFactorWitness {
    /// Check whether the position represented by this witness is healthy.
    pub fn is_healthy(&self) -> bool {
        let col_value = self.collateral_value_scaled();
        let lhs = col_value * self.threshold_bps;
        let debt_scaled = self.debt_amount / SCALE_FACTOR;
        let rhs = debt_scaled * BPS_SCALE;
        lhs >= rhs
    }

    /// Compute the scaled collateral value.
    fn collateral_value_scaled(&self) -> u64 {
        let mut cumulative: u64 = 0;
        for i in 0..self.collateral_amounts.len() {
            let value = (self.collateral_amounts[i] as u128 * self.collateral_prices[i] as u128
                / BPS_SCALE as u128) as u64;
            cumulative += value;
        }
        cumulative / SCALE_FACTOR
    }

    /// Generate the witness values map for the health factor circuit.
    pub fn to_witness_map(&self, num_rows: usize) -> HashMap<String, Vec<BabyBear>> {
        let col_scaled = self.collateral_value_scaled();
        let debt_scaled = self.debt_amount / SCALE_FACTOR;

        let lhs = col_scaled * self.threshold_bps;
        let rhs = debt_scaled * BPS_SCALE;

        // diff = lhs - rhs in BabyBear field
        let diff = if lhs >= rhs {
            BabyBear::from_u64(lhs - rhs)
        } else {
            let gap = rhs - lhs;
            BabyBear::new(BABYBEAR_P - (gap as u32 % BABYBEAR_P))
        };

        // diff_high_bit: 0 if diff < p/2 (healthy), 1 if diff >= p/2
        let half_p = BABYBEAR_P / 2;
        let diff_high_bit = if diff.0 <= half_p {
            BabyBear::ZERO
        } else {
            BabyBear::ONE
        };

        let mut map = HashMap::new();
        map.insert(
            "collateral_value".into(),
            vec![BabyBear::from_u64(col_scaled); num_rows],
        );
        map.insert(
            "debt_amount".into(),
            vec![BabyBear::from_u64(debt_scaled); num_rows],
        );
        map.insert(
            "threshold_bps".into(),
            vec![BabyBear::from_u64(self.threshold_bps); num_rows],
        );
        map.insert("lhs".into(), vec![BabyBear::from_u64(lhs); num_rows]);
        map.insert("rhs".into(), vec![BabyBear::from_u64(rhs); num_rows]);
        map.insert("diff".into(), vec![diff; num_rows]);
        map.insert("diff_high_bit".into(), vec![diff_high_bit; num_rows]);
        map
    }

    /// Generate the public inputs for the health factor circuit.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let col_scaled = self.collateral_value_scaled();
        let debt_scaled = self.debt_amount / SCALE_FACTOR;

        vec![
            BabyBear::from_u64(col_scaled),
            BabyBear::from_u64(debt_scaled),
            BabyBear::from_u64(self.threshold_bps),
        ]
    }
}

/// Witness for the interest accrual circuit.
#[derive(Clone, Debug)]
pub struct InterestAccrualWitness {
    /// Starting balance.
    pub start_balance: u64,
    /// Per-block rate numerator (denominator is RATE_PRECISION).
    pub rate_per_block: u64,
    /// Number of blocks to accrue over.
    pub num_blocks: usize,
}

impl InterestAccrualWitness {
    /// Compute the end balance after accrual.
    pub fn compute_end_balance(&self) -> u64 {
        let mut balance = self.start_balance;
        for _ in 0..self.num_blocks {
            let interest =
                (balance as u128 * self.rate_per_block as u128 / RATE_PRECISION as u128) as u64;
            balance += interest;
        }
        balance
    }

    /// Generate the witness values map for the interest accrual circuit.
    ///
    /// The trace length must be a power of two >= 2. Extra rows beyond num_blocks
    /// are padded with the final balance held constant (zero interest).
    pub fn to_witness_map(&self, num_rows: usize) -> HashMap<String, Vec<BabyBear>> {
        let mut block_indices = Vec::with_capacity(num_rows);
        let mut balances = Vec::with_capacity(num_rows);
        let mut rates = Vec::with_capacity(num_rows);
        let mut interests = Vec::with_capacity(num_rows);
        let mut next_balances = Vec::with_capacity(num_rows);

        let mut balance = self.start_balance;

        for i in 0..num_rows {
            block_indices.push(BabyBear::new(i as u32));

            if i < self.num_blocks {
                let interest =
                    (balance as u128 * self.rate_per_block as u128 / RATE_PRECISION as u128) as u64;
                let next_balance = balance + interest;

                balances.push(BabyBear::from_u64(balance));
                rates.push(BabyBear::from_u64(self.rate_per_block));
                interests.push(BabyBear::from_u64(interest));
                next_balances.push(BabyBear::from_u64(next_balance));

                balance = next_balance;
            } else {
                // Padding rows: balance stays constant, interest is zero
                balances.push(BabyBear::from_u64(balance));
                rates.push(BabyBear::from_u64(self.rate_per_block));
                interests.push(BabyBear::ZERO);
                next_balances.push(BabyBear::from_u64(balance));
            }
        }

        let mut map = HashMap::new();
        map.insert("block_index".into(), block_indices);
        map.insert("balance".into(), balances);
        map.insert("rate".into(), rates);
        map.insert("interest".into(), interests);
        map.insert("next_balance".into(), next_balances);
        map
    }

    /// Generate the public inputs for the interest accrual circuit.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let end_balance = self.compute_end_balance();
        vec![
            BabyBear::from_u64(self.start_balance),
            BabyBear::from_u64(end_balance),
            BabyBear::from_u64(self.rate_per_block),
            BabyBear::new(self.num_blocks as u32),
        ]
    }
}

// =============================================================================
// Prove / Verify API
// =============================================================================

/// Prove that a lending position's health factor is sufficient.
///
/// Returns the STARK proof bytes if the position is healthy, or an error if
/// the constraint system rejects the witness (under-collateralized).
pub fn prove_health_factor(witness: &HealthFactorWitness) -> Result<Vec<u8>, String> {
    let program = health_factor_cell_program();
    let num_rows = 2; // Minimum power-of-two trace
    let witness_map = witness.to_witness_map(num_rows);
    let public_inputs = witness.public_inputs();

    program
        .prove_transition(&witness_map, num_rows, &public_inputs)
        .map_err(|e| format!("Health factor proof generation failed: {e}"))
}

/// Verify a health factor STARK proof against public inputs.
pub fn verify_health_factor_proof(
    proof_bytes: &[u8],
    witness: &HealthFactorWitness,
) -> Result<(), String> {
    let program = health_factor_cell_program();
    let public_inputs = witness.public_inputs();

    program
        .verify_transition(&public_inputs, proof_bytes)
        .map_err(|e| format!("Health factor proof verification failed: {e}"))
}

/// Prove correct interest accrual over a period.
///
/// Returns the STARK proof bytes on success.
pub fn prove_interest_accrual(witness: &InterestAccrualWitness) -> Result<Vec<u8>, String> {
    let program = interest_accrual_cell_program();
    // Trace length must be power of two >= 2
    let num_rows = witness.num_blocks.max(2).next_power_of_two();
    let witness_map = witness.to_witness_map(num_rows);
    let public_inputs = witness.public_inputs();

    program
        .prove_transition(&witness_map, num_rows, &public_inputs)
        .map_err(|e| format!("Interest accrual proof generation failed: {e}"))
}

/// Verify an interest accrual STARK proof against public inputs.
pub fn verify_interest_accrual_proof(
    proof_bytes: &[u8],
    witness: &InterestAccrualWitness,
) -> Result<(), String> {
    let program = interest_accrual_cell_program();
    let public_inputs = witness.public_inputs();

    program
        .verify_transition(&public_inputs, proof_bytes)
        .map_err(|e| format!("Interest accrual proof verification failed: {e}"))
}

// =============================================================================
// Descriptors (for serialization and use in obligations)
// =============================================================================

/// Descriptor for health factor proofs, suitable for use in obligation conditions.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HealthFactorDescriptor {
    /// Collateral amounts per asset.
    pub collateral_amounts: Vec<u64>,
    /// Collateral prices per asset (must match amounts length).
    pub collateral_prices: Vec<u64>,
    /// Total debt value.
    pub debt_amount: u64,
    /// Liquidation threshold in basis points.
    pub threshold_bps: u64,
}

impl HealthFactorDescriptor {
    /// Build a witness from this descriptor.
    pub fn to_witness(&self) -> HealthFactorWitness {
        HealthFactorWitness {
            collateral_amounts: self.collateral_amounts.clone(),
            collateral_prices: self.collateral_prices.clone(),
            debt_amount: self.debt_amount,
            threshold_bps: self.threshold_bps,
        }
    }

    /// Check if this descriptor represents a healthy position.
    pub fn is_healthy(&self) -> bool {
        self.to_witness().is_healthy()
    }

    /// Generate a STARK proof of health.
    pub fn prove(&self) -> Result<Vec<u8>, String> {
        prove_health_factor(&self.to_witness())
    }

    /// Verify a STARK proof of health.
    pub fn verify(&self, proof_bytes: &[u8]) -> Result<(), String> {
        verify_health_factor_proof(proof_bytes, &self.to_witness())
    }
}

/// Descriptor for interest accrual proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InterestAccrualDescriptor {
    /// Starting balance.
    pub start_balance: u64,
    /// Per-block rate numerator (denominator is RATE_PRECISION).
    pub rate_per_block: u64,
    /// Number of blocks to accrue over.
    pub num_blocks: usize,
    /// Expected end balance after accrual.
    pub expected_end_balance: u64,
}

impl InterestAccrualDescriptor {
    /// Build a witness from this descriptor.
    pub fn to_witness(&self) -> InterestAccrualWitness {
        InterestAccrualWitness {
            start_balance: self.start_balance,
            rate_per_block: self.rate_per_block,
            num_blocks: self.num_blocks,
        }
    }

    /// Compute the expected end balance for this descriptor.
    pub fn compute_end_balance(&self) -> u64 {
        self.to_witness().compute_end_balance()
    }

    /// Verify the accrual computation matches expected_end_balance, then produce a STARK proof.
    pub fn prove(&self) -> Result<Vec<u8>, String> {
        let witness = self.to_witness();
        let computed_end = witness.compute_end_balance();
        if computed_end != self.expected_end_balance {
            return Err(format!(
                "End balance mismatch: computed {} but expected {}",
                computed_end, self.expected_end_balance
            ));
        }
        prove_interest_accrual(&witness)
    }

    /// Verify a STARK proof of interest accrual.
    pub fn verify_proof(&self, proof_bytes: &[u8]) -> Result<(), String> {
        verify_interest_accrual_proof(proof_bytes, &self.to_witness())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn health_factor_descriptor_validates() {
        let desc = health_factor_circuit_descriptor();
        assert!(desc.validate().is_ok());
    }

    #[test]
    fn interest_accrual_descriptor_validates() {
        let desc = interest_accrual_circuit_descriptor();
        assert!(desc.validate().is_ok());
    }

    #[test]
    fn health_factor_cell_program_deploys() {
        let mut registry = ProgramRegistry::new();
        let vk = deploy_health_factor_program(&mut registry);
        assert!(vk.is_ok());
        assert!(registry.contains(&vk.unwrap()));
    }

    #[test]
    fn interest_accrual_cell_program_deploys() {
        let mut registry = ProgramRegistry::new();
        let vk = deploy_interest_accrual_program(&mut registry);
        assert!(vk.is_ok());
        assert!(registry.contains(&vk.unwrap()));
    }

    #[test]
    fn test_health_factor_healthy_proves() {
        // 1.5M collateral at price 1:1, 1M debt, 80% threshold
        let witness = HealthFactorWitness {
            collateral_amounts: vec![1_500_000],
            collateral_prices: vec![BPS_SCALE],
            debt_amount: 1_000_000,
            threshold_bps: 8_000,
        };
        assert!(witness.is_healthy());
        let proof = prove_health_factor(&witness);
        assert!(
            proof.is_ok(),
            "Healthy position should prove: {:?}",
            proof.err()
        );

        // Verify
        let proof_bytes = proof.unwrap();
        let result = verify_health_factor_proof(&proof_bytes, &witness);
        assert!(result.is_ok(), "Proof should verify: {:?}", result.err());
    }

    #[test]
    fn test_health_factor_multi_asset() {
        // Two assets: 500K at price 2x, 300K at price 1x
        let witness = HealthFactorWitness {
            collateral_amounts: vec![500_000, 300_000],
            collateral_prices: vec![BPS_SCALE * 2, BPS_SCALE],
            debt_amount: 1_000_000,
            threshold_bps: 8_000,
        };
        assert!(witness.is_healthy());
        let proof = prove_health_factor(&witness);
        assert!(
            proof.is_ok(),
            "Multi-asset healthy position should prove: {:?}",
            proof.err()
        );
    }

    #[test]
    fn test_interest_accrual_proves() {
        let witness = InterestAccrualWitness {
            start_balance: 1_000_000,
            rate_per_block: RATE_PRECISION / 100, // 1% per block
            num_blocks: 4,                        // power of two for clean trace
        };
        let end = witness.compute_end_balance();
        assert!(end > 1_000_000);

        let proof = prove_interest_accrual(&witness);
        assert!(
            proof.is_ok(),
            "Interest accrual should prove: {:?}",
            proof.err()
        );

        let proof_bytes = proof.unwrap();
        let result = verify_interest_accrual_proof(&proof_bytes, &witness);
        assert!(result.is_ok(), "Proof should verify: {:?}", result.err());
    }

    #[test]
    fn test_interest_accrual_descriptor() {
        let witness = InterestAccrualWitness {
            start_balance: 1_000_000,
            rate_per_block: RATE_PRECISION / 1000, // 0.1% per block
            num_blocks: 4,
        };
        let end = witness.compute_end_balance();
        assert!(end > 1_000_000);

        let desc = InterestAccrualDescriptor {
            start_balance: 1_000_000,
            rate_per_block: RATE_PRECISION / 1000,
            num_blocks: 4,
            expected_end_balance: end,
        };
        let proof = desc.prove();
        assert!(proof.is_ok(), "Descriptor prove failed: {:?}", proof.err());
    }

    #[test]
    fn test_health_factor_descriptor_api() {
        let desc = HealthFactorDescriptor {
            collateral_amounts: vec![2_000_000],
            collateral_prices: vec![BPS_SCALE],
            debt_amount: 1_000_000,
            threshold_bps: 8_000,
        };
        assert!(desc.is_healthy());
        let proof = desc.prove();
        assert!(proof.is_ok(), "Descriptor prove failed: {:?}", proof.err());

        let proof_bytes = proof.unwrap();
        let result = desc.verify(&proof_bytes);
        assert!(
            result.is_ok(),
            "Descriptor verify failed: {:?}",
            result.err()
        );
    }
}
