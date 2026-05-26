//! Sovereign Cell State Transition AIR expressed as a CircuitDescriptor.
//!
//! Proves: "given old_state, applying a Transfer effect produces new_state with
//! correct balance accounting."
//!
//! # Constraint strategy
//!
//! The hand-written AIR (`circuit/src/sovereign_transition_air.rs`) enforces:
//!
//! - C1: `direction * (direction - 1) == 0` (direction is boolean)
//! - C2: `new_balance - old_balance - transfer_amount + 2*direction*transfer_amount == 0`
//!
//! If direction=1 (outgoing): new = old - amount
//! If direction=0 (incoming): new = old + amount
//!
//! # Trace Layout (2 rows, power-of-two padded)
//!
//! | Col | Name             | Description                         |
//! |-----|------------------|-------------------------------------|
//! | 0   | old_balance      | Cell balance before transfer        |
//! | 1   | transfer_amount  | Amount being transferred            |
//! | 2   | new_balance      | Cell balance after transfer         |
//! | 3   | direction        | 1=outgoing (debit), 0=incoming      |
//! | 4   | pad0             | Unused padding                      |
//! | 5   | pad1             | Unused padding                      |
//!
//! # Public Inputs (32 BabyBear elements)
//!
//! [old_commitment[0..8], new_commitment[0..8], effects_hash[0..8], cell_id_hash[0..8]]
//!
//! Each 32-byte hash is encoded as 8 BabyBear elements (4 bytes LE, reduced mod p).

use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_dsl_runtime::circuit::{
    CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit, PolyTerm,
};

/// Column indices.
pub mod col {
    pub const OLD_BALANCE: usize = 0;
    pub const TRANSFER_AMOUNT: usize = 1;
    pub const NEW_BALANCE: usize = 2;
    pub const DIRECTION: usize = 3;
    pub const PAD0: usize = 4;
    pub const PAD1: usize = 5;
}

/// Trace width for the sovereign transition DSL circuit.
pub const SOVEREIGN_DSL_WIDTH: usize = 6;

/// Number of public inputs (4 hashes * 8 field elements each).
pub const SOVEREIGN_DSL_PUBLIC_INPUTS: usize = 32;

/// Build the sovereign transition CircuitDescriptor.
///
/// Constraints:
///   C1: direction is boolean — `Binary { col: 3 }`
///   C2: balance conservation — polynomial:
///       `new_balance - old_balance - transfer_amount + 2*direction*transfer_amount == 0`
pub fn sovereign_transition_circuit_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);
    let two = BabyBear::new(2);

    let constraints = vec![
        // C1: direction is boolean
        ConstraintExpr::Binary {
            col: col::DIRECTION,
        },
        // C2: balance conservation polynomial
        // new_balance - old_balance - transfer_amount + 2*direction*transfer_amount == 0
        ConstraintExpr::Polynomial {
            terms: vec![
                // +1 * new_balance
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::NEW_BALANCE],
                },
                // -1 * old_balance
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![col::OLD_BALANCE],
                },
                // -1 * transfer_amount
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![col::TRANSFER_AMOUNT],
                },
                // +2 * direction * transfer_amount
                PolyTerm {
                    coeff: two,
                    col_indices: vec![col::DIRECTION, col::TRANSFER_AMOUNT],
                },
            ],
        },
    ];

    // No boundary constraints — commitment binding is verified externally.
    let boundaries = vec![];

    let columns = vec![
        ColumnDef {
            name: "old_balance".into(),
            index: col::OLD_BALANCE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "transfer_amount".into(),
            index: col::TRANSFER_AMOUNT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "new_balance".into(),
            index: col::NEW_BALANCE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "direction".into(),
            index: col::DIRECTION,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "pad0".into(),
            index: col::PAD0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "pad1".into(),
            index: col::PAD1,
            kind: ColumnKind::Value,
        },
    ];

    CircuitDescriptor {
        name: "dregg-sovereign-transition-dsl-v1".into(),
        trace_width: SOVEREIGN_DSL_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: SOVEREIGN_DSL_PUBLIC_INPUTS,
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the sovereign transition descriptor.
pub fn sovereign_transition_dsl_circuit() -> DslCircuit {
    DslCircuit::new(sovereign_transition_circuit_descriptor())
}

/// Generate a valid sovereign transition trace.
///
/// Returns a 2-row trace (power-of-two padded) and 32 public inputs.
///
/// # Arguments
///
/// * `old_balance` - Cell balance before transfer
/// * `transfer_amount` - Amount being transferred
/// * `direction` - 1 for outgoing (debit), 0 for incoming (credit)
/// * `old_commitment` - 32-byte commitment hash of old state
/// * `new_commitment` - 32-byte commitment hash of new state
/// * `effects_hash` - 32-byte hash of effects being applied
/// * `cell_id_hash` - 32-byte hash of the cell ID
pub fn generate_sovereign_transition_trace(
    old_balance: u64,
    transfer_amount: u64,
    direction: u32,
    old_commitment: &[u8; 32],
    new_commitment: &[u8; 32],
    effects_hash: &[u8; 32],
    cell_id_hash: &[u8; 32],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let new_balance = if direction == 1 {
        old_balance.saturating_sub(transfer_amount)
    } else {
        old_balance.saturating_add(transfer_amount)
    };

    let row = vec![
        BabyBear::from_u64(old_balance),
        BabyBear::from_u64(transfer_amount),
        BabyBear::from_u64(new_balance),
        BabyBear::new(direction),
        BabyBear::ZERO,
        BabyBear::ZERO,
    ];

    // 2-row trace (power-of-two, padded with duplicate).
    let trace = vec![row.clone(), row];

    // Public inputs: 4 hashes * 8 BabyBear elements each = 32.
    let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_DSL_PUBLIC_INPUTS);
    public_inputs.extend(bytes32_to_babybear(old_commitment));
    public_inputs.extend(bytes32_to_babybear(new_commitment));
    public_inputs.extend(bytes32_to_babybear(effects_hash));
    public_inputs.extend(bytes32_to_babybear(cell_id_hash));

    (trace, public_inputs)
}

/// Encode a 32-byte hash as 8 BabyBear field elements (4 bytes each, little-endian).
fn bytes32_to_babybear(bytes: &[u8; 32]) -> Vec<BabyBear> {
    let mut result = Vec::with_capacity(8);
    for chunk in bytes.chunks(4) {
        let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        result.push(BabyBear::new(val % BABYBEAR_P));
    }
    result
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::stark::{self, StarkAir};

    #[test]
    fn descriptor_has_correct_structure() {
        let desc = sovereign_transition_circuit_descriptor();
        assert_eq!(desc.trace_width, SOVEREIGN_DSL_WIDTH);
        assert_eq!(desc.public_input_count, SOVEREIGN_DSL_PUBLIC_INPUTS);
        assert_eq!(desc.name, "dregg-sovereign-transition-dsl-v1");
        assert_eq!(desc.max_degree, 2);

        // Should have: 1 Binary + 1 Polynomial = 2 constraints
        assert_eq!(desc.constraints.len(), 2);

        // No boundary constraints (commitment binding is external)
        assert_eq!(desc.boundaries.len(), 0);

        // 6 columns
        assert_eq!(desc.columns.len(), 6);
    }

    #[test]
    fn descriptor_validates() {
        let desc = sovereign_transition_circuit_descriptor();
        assert!(
            desc.validate().is_ok(),
            "sovereign transition descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn valid_trace_evaluates_to_zero() {
        // Outgoing: 1000 - 100 = 900
        let (trace, pi) = generate_sovereign_transition_trace(
            1000, 100, 1, &[1u8; 32], &[2u8; 32], &[3u8; 32], &[4u8; 32],
        );
        let circuit = sovereign_transition_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Valid outgoing trace should satisfy all constraints"
        );

        // Incoming: 500 + 200 = 700
        let (trace, pi) = generate_sovereign_transition_trace(
            500,
            200,
            0,
            &[10u8; 32],
            &[11u8; 32],
            &[12u8; 32],
            &[13u8; 32],
        );
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Valid incoming trace should satisfy all constraints"
        );
    }

    #[test]
    fn tampered_new_balance_detected() {
        let (mut trace, pi) = generate_sovereign_transition_trace(
            1000, 100, 1, &[1u8; 32], &[2u8; 32], &[3u8; 32], &[4u8; 32],
        );
        let circuit = sovereign_transition_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: set new_balance to 1000 instead of correct 900
        trace[0][col::NEW_BALANCE] = BabyBear::from_u64(1000);
        trace[1][col::NEW_BALANCE] = BabyBear::from_u64(1000);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered new_balance should violate balance conservation"
        );
    }

    #[test]
    fn non_binary_direction_detected() {
        let circuit = sovereign_transition_dsl_circuit();
        let alpha = BabyBear::new(7);
        let dummy_pi = vec![BabyBear::ZERO; 32];

        // direction = 2 (invalid)
        let row = vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(900),
            BabyBear::new(2), // INVALID direction
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];

        let result = circuit.eval_constraints(&row, &row, &dummy_pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Non-binary direction should violate Binary constraint"
        );
    }

    #[test]
    fn wrong_direction_detected() {
        let circuit = sovereign_transition_dsl_circuit();
        let alpha = BabyBear::new(7);
        let dummy_pi = vec![BabyBear::ZERO; 32];

        // old=1000, amount=100, direction=0 (incoming) => correct new=1100
        // But we claim new=900 (which would be correct for outgoing)
        let row = vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(900),
            BabyBear::ZERO, // incoming
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];

        let result = circuit.eval_constraints(&row, &row, &dummy_pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Wrong direction/balance combination should violate conservation constraint"
        );
    }

    #[test]
    fn stark_prove_verify() {
        let (trace, pi) = generate_sovereign_transition_trace(
            1000, 100, 1, &[1u8; 32], &[2u8; 32], &[3u8; 32], &[4u8; 32],
        );
        let circuit = sovereign_transition_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify should succeed on valid outgoing trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn stark_prove_verify_incoming() {
        let (trace, pi) = generate_sovereign_transition_trace(
            500,
            200,
            0,
            &[10u8; 32],
            &[11u8; 32],
            &[12u8; 32],
            &[13u8; 32],
        );
        let circuit = sovereign_transition_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify should succeed on valid incoming trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn stark_rejects_invalid_trace() {
        // Build invalid trace: wrong new_balance
        let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_DSL_PUBLIC_INPUTS);
        public_inputs.extend(bytes32_to_babybear(&[5u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[6u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[7u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[8u8; 32]));

        let row = vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(1000), // WRONG: should be 900
            BabyBear::ONE,            // direction = outgoing
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = vec![row.clone(), row];

        let circuit = sovereign_transition_dsl_circuit();
        assert!(
            stark::try_prove(&circuit, &trace, &public_inputs).is_err(),
            "Invalid trace should not prove"
        );
    }

    #[test]
    fn stark_rejects_wrong_pi() {
        let (trace, pi) = generate_sovereign_transition_trace(
            1000, 100, 1, &[1u8; 32], &[2u8; 32], &[3u8; 32], &[4u8; 32],
        );
        let circuit = sovereign_transition_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        // Tamper with public inputs
        let mut wrong_pi = pi.clone();
        wrong_pi[0] = BabyBear::new(99999);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong public inputs"
        );
    }
}
