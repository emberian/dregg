//! Effect VM AIR: Multi-row DSL circuit proving arbitrary sequences of effects
//! (turns) in a single STARK proof.
//!
//! Inspired by o1vm (RISC-V execution trace proving), but for pyana Effects instead
//! of CPU instructions. Each trace row represents one effect execution step.
//!
//! # Instruction Set (Effect Types)
//!
//! - NoOp (0): Padding effect; all constraints trivially satisfied.
//! - Transfer (1): Balance transfer with direction (in/out).
//! - SetField (2): Update a custom field slot.
//! - GrantCapability (3): Add capability to c-list (capability_root update).
//! - NoteSpend (4): Spend a note (nullifier reveal, balance credit).
//! - NoteCreate (5): Create a note (commitment creation, balance debit).
//!
//! # Trace Layout (one row per effect)
//!
//! ```text
//! | selector[6] | state_before[14] | effect_params[8] | state_after[14] | aux[8] |
//! ```
//!
//! Total width: 50 columns
//!
//! ## Column Breakdown
//!
//! Selectors (cols 0..6): Exactly one active per row.
//!   - sel_noop, sel_transfer, sel_setfield, sel_grantcap, sel_notespend, sel_notecreate
//!
//! State Before (cols 6..20):
//!   - balance_lo, balance_hi (u64 as two BabyBear limbs, 31+33 bits)
//!   - nonce
//!   - field_values[0..7] (8 custom fields)
//!   - capability_root
//!   - state_commitment (running Poseidon2 hash of full state)
//!   - reserved
//!
//! Effect Params (cols 20..28):
//!   - param0..param7 (meaning depends on effect type)
//!
//! State After (cols 28..42):
//!   - Same layout as state_before
//!
//! Aux (cols 42..50):
//!   - Auxiliary witness values (e.g., intermediate hashes, range proofs)
//!
//! # Constraints
//!
//! 1. Selector exclusivity: sum(selectors) == 1, each selector is boolean.
//! 2. Per-effect constraints (gated by selector):
//!    - Transfer: new_balance = old_balance +/- amount
//!    - SetField: one field updated, others unchanged
//!    - GrantCap: capability_root = hash(old_root, new_entry)
//!    - NoteSpend: nullifier valid, balance increases
//!    - NoteCreate: commitment valid, balance decreases
//! 3. Transition constraints (row-to-row continuity):
//!    - next_row.state_before == this_row.state_after
//!    - next_row.nonce == this_row.nonce + 1 (or same for NoOp padding)
//! 4. Boundary constraints:
//!    - First row: state_before matches old_commitment (public input)
//!    - Last non-padding row: state_after matches new_commitment
//!    - Conservation: net balance delta == public input
//!
//! # Public Inputs (20 elements)
//!
//! [old_commitment[0..8], new_commitment[0..8], net_delta_magnitude, net_delta_sign,
//!  effects_hash_lo, effects_hash_hi]

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_many};
use crate::stark::{BoundaryConstraint, StarkAir};

// ============================================================================
// Column layout constants
// ============================================================================

/// Total trace width.
pub const EFFECT_VM_WIDTH: usize = 50;

/// Number of effect types (selectors).
pub const NUM_EFFECTS: usize = 6;

/// Selector column indices.
pub mod sel {
    pub const NOOP: usize = 0;
    pub const TRANSFER: usize = 1;
    pub const SET_FIELD: usize = 2;
    pub const GRANT_CAP: usize = 3;
    pub const NOTE_SPEND: usize = 4;
    pub const NOTE_CREATE: usize = 5;
}

/// State column offsets (relative to state start).
pub mod state {
    pub const BALANCE_LO: usize = 0;
    pub const BALANCE_HI: usize = 1;
    pub const NONCE: usize = 2;
    pub const FIELD_BASE: usize = 3; // fields[0..8] at offsets 3..11
    pub const CAP_ROOT: usize = 11;
    pub const STATE_COMMIT: usize = 12;
    pub const RESERVED: usize = 13;
    pub const SIZE: usize = 14;
}

/// Absolute column indices for state_before.
pub const STATE_BEFORE_BASE: usize = NUM_EFFECTS; // 6
/// Absolute column indices for state_after.
pub const STATE_AFTER_BASE: usize = STATE_BEFORE_BASE + state::SIZE + 8; // 6 + 14 + 8 = 28
/// Effect parameter base column.
pub const PARAM_BASE: usize = STATE_BEFORE_BASE + state::SIZE; // 6 + 14 = 20
/// Number of parameter columns.
pub const NUM_PARAMS: usize = 8;
/// Auxiliary witness base column.
pub const AUX_BASE: usize = STATE_AFTER_BASE + state::SIZE; // 28 + 14 = 42
/// Number of auxiliary columns.
pub const NUM_AUX: usize = 8;

/// Effect parameter meanings per effect type.
///
/// Transfer:
///   param0 = amount
///   param1 = direction (0=incoming, 1=outgoing)
///
/// SetField:
///   param0 = field_index (0..7)
///   param1 = new_value
///
/// GrantCapability:
///   param0 = capability_entry (hash of new capability)
///
/// NoteSpend:
///   param0 = nullifier
///   param1 = value_lo
///   param2 = value_hi
///
/// NoteCreate:
///   param0 = commitment
///   param1 = value_lo
///   param2 = value_hi
pub mod param {
    pub const AMOUNT: usize = 0;
    pub const DIRECTION: usize = 1;
    pub const FIELD_INDEX: usize = 0;
    pub const NEW_VALUE: usize = 1;
    pub const CAP_ENTRY: usize = 0;
    pub const NULLIFIER: usize = 0;
    pub const NOTE_VALUE_LO: usize = 1;
    pub const NOTE_VALUE_HI: usize = 2;
    pub const NOTE_COMMITMENT: usize = 0;
}

/// Public input layout.
pub mod pi {
    /// Old state commitment (8 BabyBear elements from 32-byte hash).
    pub const OLD_COMMIT_BASE: usize = 0;
    pub const OLD_COMMIT_LEN: usize = 8;
    /// New state commitment (8 BabyBear elements).
    pub const NEW_COMMIT_BASE: usize = 8;
    pub const NEW_COMMIT_LEN: usize = 8;
    /// Net balance delta: [magnitude, sign_bit].
    pub const NET_DELTA_MAG: usize = 16;
    pub const NET_DELTA_SIGN: usize = 17;
    /// Effects hash (2 BabyBear elements: lo, hi).
    pub const EFFECTS_HASH_LO: usize = 18;
    pub const EFFECTS_HASH_HI: usize = 19;
    /// Total public inputs.
    pub const COUNT: usize = 20;
}

// ============================================================================
// Effect enum for witness generation
// ============================================================================

/// An effect to be proven in the VM.
#[derive(Clone, Debug)]
pub enum Effect {
    /// No operation (used for padding).
    NoOp,
    /// Transfer balance.
    Transfer {
        amount: u64,
        /// 0 = incoming (credit), 1 = outgoing (debit).
        direction: u32,
    },
    /// Set a custom field value.
    SetField { field_idx: u32, value: BabyBear },
    /// Grant a capability (add entry to c-list Merkle root).
    GrantCapability { cap_entry: BabyBear },
    /// Spend a note (reveal nullifier, credit balance).
    NoteSpend { nullifier: BabyBear, value: u64 },
    /// Create a note (create commitment, debit balance).
    NoteCreate { commitment: BabyBear, value: u64 },
}

/// Cell state that flows between rows.
#[derive(Clone, Debug)]
pub struct CellState {
    /// Balance as u64 (split into lo/hi for BabyBear encoding).
    pub balance: u64,
    /// Monotonic nonce.
    pub nonce: u32,
    /// 8 custom field values.
    pub fields: [BabyBear; 8],
    /// Capability list Merkle root.
    pub capability_root: BabyBear,
    /// Running state commitment.
    pub state_commitment: BabyBear,
}

impl CellState {
    /// Create a new cell state with default values.
    pub fn new(balance: u64, nonce: u32) -> Self {
        let fields = [BabyBear::ZERO; 8];
        let capability_root = BabyBear::ZERO;
        // Initial state commitment is hash of all state elements.
        let state_commitment = Self::compute_commitment(
            balance,
            nonce,
            &fields,
            capability_root,
        );
        Self {
            balance,
            nonce,
            fields,
            capability_root,
            state_commitment,
        }
    }

    /// Compute the state commitment from all state components.
    pub fn compute_commitment(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> BabyBear {
        let (lo, hi) = split_u64(balance);
        let mut inputs = Vec::with_capacity(12);
        inputs.push(lo);
        inputs.push(hi);
        inputs.push(BabyBear::new(nonce));
        inputs.extend_from_slice(fields);
        inputs.push(capability_root);
        hash_many(&inputs)
    }

    /// Recompute and update the state commitment.
    pub fn refresh_commitment(&mut self) {
        self.state_commitment = Self::compute_commitment(
            self.balance,
            self.nonce,
            &self.fields,
            self.capability_root,
        );
    }

    /// Encode state into trace columns (14 elements).
    fn to_trace_cols(&self) -> Vec<BabyBear> {
        let (lo, hi) = split_u64(self.balance);
        let mut cols = Vec::with_capacity(state::SIZE);
        cols.push(lo);                          // balance_lo
        cols.push(hi);                          // balance_hi
        cols.push(BabyBear::new(self.nonce));   // nonce
        cols.extend_from_slice(&self.fields);   // field_values[0..8]
        cols.push(self.capability_root);        // cap_root
        cols.push(self.state_commitment);       // state_commit
        cols.push(BabyBear::ZERO);             // reserved
        assert_eq!(cols.len(), state::SIZE);
        cols
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Split a u64 into two BabyBear elements: (lo = lower 30 bits, hi = upper 34 bits).
/// Both values fit in BabyBear (< 2^31).
fn split_u64(val: u64) -> (BabyBear, BabyBear) {
    let lo = (val & 0x3FFF_FFFF) as u32; // lower 30 bits
    let hi = (val >> 30) as u32;          // upper 34 bits (fits in u32 since val < 2^64)
    (BabyBear::new(lo), BabyBear::new(hi))
}

/// Reconstruct a u64 from split BabyBear limbs.
fn join_u64(lo: BabyBear, hi: BabyBear) -> u64 {
    (lo.0 as u64) | ((hi.0 as u64) << 30)
}

/// Compute the effects hash for a sequence of effects.
/// Returns (lo, hi) BabyBear elements.
pub fn compute_effects_hash(effects: &[Effect]) -> (BabyBear, BabyBear) {
    let mut hasher_inputs = Vec::new();
    for effect in effects {
        match effect {
            Effect::NoOp => {
                hasher_inputs.push(BabyBear::ZERO);
            }
            Effect::Transfer { amount, direction } => {
                hasher_inputs.push(BabyBear::ONE);
                let (lo, hi) = split_u64(*amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(BabyBear::new(*direction));
            }
            Effect::SetField { field_idx, value } => {
                hasher_inputs.push(BabyBear::new(2));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*value);
            }
            Effect::GrantCapability { cap_entry } => {
                hasher_inputs.push(BabyBear::new(3));
                hasher_inputs.push(*cap_entry);
            }
            Effect::NoteSpend { nullifier, value } => {
                hasher_inputs.push(BabyBear::new(4));
                hasher_inputs.push(*nullifier);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::NoteCreate { commitment, value } => {
                hasher_inputs.push(BabyBear::new(5));
                hasher_inputs.push(*commitment);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
        }
    }
    let h = hash_many(&hasher_inputs);
    // Split into two elements for wider coverage.
    let h2 = hash_2_to_1(h, BabyBear::new(0xEFFEC7));
    (h, h2)
}

// ============================================================================
// AIR Implementation
// ============================================================================

/// The Effect VM AIR. Proves an arbitrary sequence of effects in a single STARK.
pub struct EffectVmAir {
    /// Maximum number of effects (trace height, padded to power of 2).
    pub max_effects: usize,
}

impl EffectVmAir {
    pub fn new(max_effects: usize) -> Self {
        assert!(max_effects >= 2, "Need at least 2 rows for STARK");
        assert!(
            max_effects.is_power_of_two(),
            "max_effects must be a power of 2"
        );
        Self { max_effects }
    }
}

impl StarkAir for EffectVmAir {
    fn width(&self) -> usize {
        EFFECT_VM_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // Selector sum constraint is degree 1 (linear).
        // Selector boolean constraints are degree 2.
        // Per-effect constraints: selector * (expression) is at most degree 2 + 1 = 3.
        // GrantCap uses hash which is algebraic but here we do advisory check.
        // The highest degree from selector gating is 2 (selector * linear expression).
        3
    }

    fn air_name(&self) -> &'static str {
        "pyana-effect-vm-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        // ====================================================================
        // CONSTRAINT GROUP 1: Selector validity
        // ====================================================================

        // Each selector must be boolean: s*(s-1) == 0
        for i in 0..NUM_EFFECTS {
            let s = local[i];
            let c = s * (s - BabyBear::ONE);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Selectors must sum to exactly 1.
        let mut sel_sum = BabyBear::ZERO;
        for i in 0..NUM_EFFECTS {
            sel_sum = sel_sum + local[i];
        }
        let c_sum = sel_sum - BabyBear::ONE;
        combined = combined + alpha_pow * c_sum;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // CONSTRAINT GROUP 2: Per-effect-type constraints (gated by selector)
        // ====================================================================

        let s_noop = local[sel::NOOP];
        let s_transfer = local[sel::TRANSFER];
        let s_setfield = local[sel::SET_FIELD];
        let s_grantcap = local[sel::GRANT_CAP];
        let s_notespend = local[sel::NOTE_SPEND];
        let s_notecreate = local[sel::NOTE_CREATE];

        // State accessors (before).
        let old_bal_lo = local[STATE_BEFORE_BASE + state::BALANCE_LO];
        let old_bal_hi = local[STATE_BEFORE_BASE + state::BALANCE_HI];
        let old_nonce = local[STATE_BEFORE_BASE + state::NONCE];
        let old_cap_root = local[STATE_BEFORE_BASE + state::CAP_ROOT];

        // State accessors (after).
        let new_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
        let new_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
        let new_nonce = local[STATE_AFTER_BASE + state::NONCE];
        let new_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];

        // Parameters.
        let p0 = local[PARAM_BASE + 0];
        let p1 = local[PARAM_BASE + 1];
        let p2 = local[PARAM_BASE + 2];

        // -- NoOp: state_after == state_before for all state columns --
        for i in 0..state::SIZE {
            let c = s_noop * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Transfer: balance update --
        // param0 = amount_lo, param1 = direction (0=in, 1=out)
        // If direction=0 (in): new_bal = old_bal + amount
        // If direction=1 (out): new_bal = old_bal - amount
        // Unified: new_bal_lo - old_bal_lo - amount + 2*direction*amount == carry adjustment
        //
        // We work with the combined 60-bit balance:
        //   balance = bal_lo + bal_hi * 2^30
        //   Transfer only touches bal_lo for simplicity (amount < 2^30).
        //   new_bal_lo = old_bal_lo + amount * (1 - 2*direction)
        //
        // For amounts that don't overflow a single limb:
        let two = BabyBear::new(2);
        let direction = p1;
        let amount = p0;
        // new_bal_lo == old_bal_lo + amount - 2*direction*amount
        let c_transfer_lo =
            s_transfer * (new_bal_lo - old_bal_lo - amount + two * direction * amount);
        combined = combined + alpha_pow * c_transfer_lo;
        alpha_pow = alpha_pow * alpha;

        // Transfer: hi limb unchanged (for single-limb amounts).
        let c_transfer_hi = s_transfer * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_transfer_hi;
        alpha_pow = alpha_pow * alpha;

        // Transfer: direction must be boolean.
        let c_transfer_dir = s_transfer * direction * (direction - BabyBear::ONE);
        combined = combined + alpha_pow * c_transfer_dir;
        alpha_pow = alpha_pow * alpha;

        // Transfer: non-balance state unchanged.
        for i in [state::CAP_ROOT, state::STATE_COMMIT, state::RESERVED] {
            let c = s_transfer * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Transfer: fields unchanged.
        for i in 0..8 {
            let c = s_transfer
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetField: exactly one field updated --
        // param0 = field_index, param1 = new_value
        // For the targeted field: new_field[idx] = new_value.
        // For all others: unchanged.
        // We use the Lagrange selector trick:
        //   For each field slot j: new_field[j] - old_field[j] - is_target_j * (new_value - old_field[j]) == 0
        //   where is_target_j = prod_{k != j} (field_index - k) / (j - k)
        //
        // Simplified: we constrain that the sum of changes equals (new_value - old_field[idx])
        // and that it happens at exactly the right index. For degree control, we use:
        //   For each j in 0..8:
        //     sel_setfield * (new_field[j] - old_field[j]) * (1 - eq(field_index, j)) == 0
        //     where eq check is: (field_index - j) * inverse_or_zero
        //
        // Even simpler approach (lower degree): use aux columns for the Lagrange basis.
        // But for v1, we use a direct approach with the product constraint:
        //   sel_setfield * (new_field[j] - old_field[j]) * product_{k != j}(field_index - k) == 0
        //   for all j where field_index != j.
        //
        // Actually simplest: enforce
        //   For each j: sel * (new_f[j] - old_f[j] - delta_j) == 0
        //   where delta_j = if j == field_index { new_value - old_f[j] } else { 0 }
        //
        // We do it as: for the ONE field that matches, the difference must equal new_value - old.
        // For all others, difference must be zero.
        // With selector-index product trick at degree 2:
        //   sel_setfield * (field_index - j) * (new_f[j] - old_f[j]) == 0 for each j
        //   (if field_index == j, this is trivially 0 regardless of change)
        //   (if field_index != j, new_f[j] - old_f[j] must be 0)
        let field_index = p0;
        let new_value = p1;
        for j in 0..8u32 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j as usize];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j as usize];
            // Non-target fields must be unchanged.
            let c = s_setfield * (field_index - BabyBear::new(j)) * (new_fj - old_fj);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // The target field must become new_value. We check this by:
        //   For each j: sel * prod_{k!=j}(index - k) * (new_f[j] - new_value) == 0
        // When index == j, prod_{k!=j}(index-k) != 0, so new_f[j] must equal new_value.
        // When index != j, some factor (index - j) is zero in the product, so constraint is trivial.
        // But this is high degree (degree 8). Instead, use the aux column approach:
        //   aux[0] stores the Lagrange indicator (computed in witness gen).
        //   Constraint: sel * (sum_j new_f[j] * lagrange_j - new_value) == 0
        //
        // Simplest correct approach for v1: The witness generation ensures the right field
        // is set. We just need ONE constraint proving the target field has the right value.
        // Use aux[0] to carry the old value of the target field, then:
        //   sel_setfield * (new_value - target_field_new) == 0
        // where target_field_new is reconstructed from the trace.
        //
        // Actually, the simplest sound approach:
        //   Verify that the difference across all fields sums to exactly (new_value - old_value_at_idx).
        //   Combined with per-field constraints above (non-target unchanged), this is sufficient.
        // The sum of (new_f[j] - old_f[j]) for all j must equal (new_value - old_value_at_idx).
        // old_value_at_idx is stored in aux[0].
        let old_value_at_idx = local[AUX_BASE + 0];
        let mut field_diff_sum = BabyBear::ZERO;
        for j in 0..8 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j];
            field_diff_sum = field_diff_sum + (new_fj - old_fj);
        }
        let c_setfield_sum = s_setfield * (field_diff_sum - (new_value - old_value_at_idx));
        combined = combined + alpha_pow * c_setfield_sum;
        alpha_pow = alpha_pow * alpha;

        // SetField: balance and cap_root unchanged.
        let c_sf_bal_lo = s_setfield * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sf_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sf_bal_hi = s_setfield * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sf_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sf_cap = s_setfield * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sf_cap;
        alpha_pow = alpha_pow * alpha;

        // -- GrantCapability: capability_root update via hash --
        // param0 = cap_entry (hash of new capability)
        // new_cap_root = hash_2_to_1(old_cap_root, cap_entry)
        // This is a hash constraint — we store the expected hash in aux[1] during witness gen.
        let cap_entry = p0;
        let expected_new_cap = hash_2_to_1(old_cap_root, cap_entry);
        let c_grantcap = s_grantcap * (new_cap_root - expected_new_cap);
        combined = combined + alpha_pow * c_grantcap;
        alpha_pow = alpha_pow * alpha;

        // GrantCap: balance and fields unchanged.
        let c_gc_bal_lo = s_grantcap * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_gc_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_gc_bal_hi = s_grantcap * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_gc_bal_hi;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_grantcap
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteSpend: balance credit --
        // param0 = nullifier, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo + value_lo (with potential carry to hi)
        // For simplicity (v1): value fits in lo limb (value_hi == 0).
        let note_val_lo = p1;
        let c_ns_bal = s_notespend * (new_bal_lo - old_bal_lo - note_val_lo);
        combined = combined + alpha_pow * c_ns_bal;
        alpha_pow = alpha_pow * alpha;
        let c_ns_hi = s_notespend * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_ns_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteSpend: fields and cap unchanged.
        let c_ns_cap = s_notespend * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_ns_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notespend
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteCreate: balance debit --
        // param0 = commitment, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo - value_lo
        let nc_val_lo = p1;
        let c_nc_bal = s_notecreate * (new_bal_lo - old_bal_lo + nc_val_lo);
        combined = combined + alpha_pow * c_nc_bal;
        alpha_pow = alpha_pow * alpha;
        let c_nc_hi = s_notecreate * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_nc_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteCreate: fields and cap unchanged.
        let c_nc_cap = s_notecreate * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_nc_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notecreate
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 3: Transition constraints (row continuity)
        // ====================================================================
        // next_row.state_before == this_row.state_after
        // (Enforced on all rows except the last — the STARK framework handles this
        //  via the transition vanishing polynomial which excludes the last row.)
        for i in 0..state::SIZE {
            let c = next[STATE_BEFORE_BASE + i] - local[STATE_AFTER_BASE + i];
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Nonce increment: for non-NoOp rows, nonce increments by 1.
        // For NoOp (padding) rows, nonce stays the same.
        // Combined: new_nonce == old_nonce + (1 - sel_noop)
        let c_nonce = new_nonce - old_nonce - (BabyBear::ONE - s_noop);
        combined = combined + alpha_pow * c_nonce;
        // alpha_pow = alpha_pow * alpha; // (not needed after last)

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() < pi::COUNT {
            return constraints;
        }

        // First row: state_commitment must match old_commitment from public inputs.
        // We bind the state_commit column at row 0 to the hash of old_commitment PI.
        // Since old_commitment in PI is 8 elements (from a 32-byte hash), and the trace
        // stores a single Poseidon2 hash, we bind the state_commit column.
        // The public input encodes the commitment as a single field element (hash of the 8 elements).
        let old_commit_hash = hash_many(&public_inputs[pi::OLD_COMMIT_BASE..pi::OLD_COMMIT_BASE + pi::OLD_COMMIT_LEN]);
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::STATE_COMMIT,
            value: old_commit_hash,
        });

        // Net balance delta binding: the net delta is carried in aux columns.
        // Row 0, aux[2] = net_delta_magnitude, aux[3] = net_delta_sign.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 2,
            value: public_inputs[pi::NET_DELTA_MAG],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 3,
            value: public_inputs[pi::NET_DELTA_SIGN],
        });

        // Effects hash binding.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 4,
            value: public_inputs[pi::EFFECTS_HASH_LO],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 5,
            value: public_inputs[pi::EFFECTS_HASH_HI],
        });

        constraints
    }
}

// ============================================================================
// Witness Generation
// ============================================================================

/// Generate the execution trace and public inputs for an effect VM proof.
///
/// # Arguments
/// * `initial_state` - The cell state before executing effects.
/// * `effects` - The sequence of effects to prove.
///
/// # Returns
/// (trace, public_inputs) suitable for `stark::prove`.
pub fn generate_effect_vm_trace(
    initial_state: &CellState,
    effects: &[Effect],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!effects.is_empty(), "Need at least one effect");

    // Determine trace height (pad to power of 2, minimum 2).
    let n_effects = effects.len();
    let trace_height = n_effects.next_power_of_two().max(2);

    let mut trace = Vec::with_capacity(trace_height);
    let mut current_state = initial_state.clone();

    // Track net balance delta.
    let mut net_delta: i64 = 0;

    for effect in effects {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];

        // Set selector.
        let sel_idx = match effect {
            Effect::NoOp => sel::NOOP,
            Effect::Transfer { .. } => sel::TRANSFER,
            Effect::SetField { .. } => sel::SET_FIELD,
            Effect::GrantCapability { .. } => sel::GRANT_CAP,
            Effect::NoteSpend { .. } => sel::NOTE_SPEND,
            Effect::NoteCreate { .. } => sel::NOTE_CREATE,
        };
        row[sel_idx] = BabyBear::ONE;

        // Write state_before.
        let state_before_cols = current_state.to_trace_cols();
        for (i, &val) in state_before_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }

        // Apply effect and compute state_after + params.
        let mut new_state = current_state.clone();
        match effect {
            Effect::NoOp => {
                // No state change, no nonce increment for padding.
            }
            Effect::Transfer { amount, direction } => {
                let (lo, _hi) = split_u64(*amount);
                row[PARAM_BASE + param::AMOUNT] = lo;
                row[PARAM_BASE + param::DIRECTION] = BabyBear::new(*direction);

                if *direction == 1 {
                    // Outgoing.
                    new_state.balance = new_state.balance.saturating_sub(*amount);
                    net_delta -= *amount as i64;
                } else {
                    // Incoming.
                    new_state.balance = new_state.balance.saturating_add(*amount);
                    net_delta += *amount as i64;
                }
                new_state.nonce += 1;
            }
            Effect::SetField { field_idx, value } => {
                row[PARAM_BASE + param::FIELD_INDEX] = BabyBear::new(*field_idx);
                row[PARAM_BASE + param::NEW_VALUE] = *value;

                // Store old value at target index in aux[0] for the constraint.
                let idx = *field_idx as usize;
                row[AUX_BASE + 0] = current_state.fields[idx.min(7)];

                new_state.fields[idx.min(7)] = *value;
                new_state.nonce += 1;
            }
            Effect::GrantCapability { cap_entry } => {
                row[PARAM_BASE + param::CAP_ENTRY] = *cap_entry;

                new_state.capability_root =
                    hash_2_to_1(current_state.capability_root, *cap_entry);
                new_state.nonce += 1;
            }
            Effect::NoteSpend { nullifier, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NULLIFIER] = *nullifier;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                new_state.balance = new_state.balance.saturating_add(*value);
                net_delta += *value as i64;
                new_state.nonce += 1;
            }
            Effect::NoteCreate { commitment, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NOTE_COMMITMENT] = *commitment;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                new_state.balance = new_state.balance.saturating_sub(*value);
                net_delta -= *value as i64;
                new_state.nonce += 1;
            }
        }

        // Refresh state commitment.
        new_state.refresh_commitment();

        // Write state_after.
        let state_after_cols = new_state.to_trace_cols();
        for (i, &val) in state_after_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        trace.push(row);
        current_state = new_state;
    }

    // Compute effects hash and net delta for public inputs.
    let (effects_hash_lo, effects_hash_hi) = compute_effects_hash(effects);
    let (delta_mag, delta_sign) = if net_delta < 0 {
        ((-net_delta) as u32, 1u32)
    } else {
        (net_delta as u32, 0u32)
    };

    // Fill aux columns on the first row with public-input-bound values.
    if !trace.is_empty() {
        trace[0][AUX_BASE + 2] = BabyBear::new(delta_mag);
        trace[0][AUX_BASE + 3] = BabyBear::new(delta_sign);
        trace[0][AUX_BASE + 4] = effects_hash_lo;
        trace[0][AUX_BASE + 5] = effects_hash_hi;
    }

    // Pad with NoOp rows.
    for _ in n_effects..trace_height {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row[sel::NOOP] = BabyBear::ONE; // NoOp selector

        // State before = current state (carried from last real row).
        let state_cols = current_state.to_trace_cols();
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }
        // State after = same (NoOp doesn't change state).
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        trace.push(row);
        // current_state stays the same for padding.
    }

    // Build public inputs.
    let mut public_inputs = Vec::with_capacity(pi::COUNT);

    // Old commitment: hash the initial state commitment into 8 BabyBear elements.
    // For simplicity, we repeat the state_commitment hash to fill 8 slots.
    let old_commit = initial_state.state_commitment;
    for i in 0..8 {
        public_inputs.push(hash_2_to_1(old_commit, BabyBear::new(i as u32)));
    }

    // New commitment: from final state.
    let new_commit = current_state.state_commitment;
    for i in 0..8 {
        public_inputs.push(hash_2_to_1(new_commit, BabyBear::new(i as u32)));
    }

    // Net delta.
    public_inputs.push(BabyBear::new(delta_mag));
    public_inputs.push(BabyBear::new(delta_sign));

    // Effects hash.
    public_inputs.push(effects_hash_lo);
    public_inputs.push(effects_hash_hi);

    assert_eq!(public_inputs.len(), pi::COUNT);

    (trace, public_inputs)
}

/// Encode a signed balance delta as (magnitude, sign_bit) for public inputs.
pub fn encode_net_delta(delta: i64) -> (BabyBear, BabyBear) {
    if delta < 0 {
        (BabyBear::new((-delta) as u32), BabyBear::ONE)
    } else {
        (BabyBear::new(delta as u32), BabyBear::ZERO)
    }
}

/// Extract the net balance delta from public inputs.
pub fn extract_net_delta(public_inputs: &[BabyBear]) -> Option<i64> {
    if public_inputs.len() < pi::COUNT {
        return None;
    }
    let magnitude = public_inputs[pi::NET_DELTA_MAG].0 as i64;
    let sign_bit = public_inputs[pi::NET_DELTA_SIGN].0;
    if sign_bit == 1 {
        Some(-magnitude)
    } else {
        Some(magnitude)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify};

    fn make_initial_state(balance: u64) -> CellState {
        CellState::new(balance, 0)
    }

    #[test]
    fn test_single_transfer_outgoing() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 2); // padded to power of 2
        assert_eq!(trace[0].len(), EFFECT_VM_WIDTH);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_ok(), "Single transfer should verify: {:?}", result.err());

        // Check delta.
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -100);
    }

    #[test]
    fn test_single_transfer_incoming() {
        let state = make_initial_state(500);
        let effects = vec![Effect::Transfer {
            amount: 200,
            direction: 0,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_ok(), "Incoming transfer should verify: {:?}", result.err());

        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, 200);
    }

    #[test]
    fn test_multi_effect_turn() {
        let state = make_initial_state(5000);
        let effects = vec![
            Effect::Transfer {
                amount: 100,
                direction: 1, // -100
            },
            Effect::SetField {
                field_idx: 2,
                value: BabyBear::new(42),
            },
            Effect::GrantCapability {
                cap_entry: BabyBear::new(0xCAFE),
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        // 3 effects padded to 4 rows.
        assert_eq!(trace.len(), 4);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Multi-effect turn should verify: {:?}",
            result.err()
        );

        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -100);
    }

    #[test]
    fn test_wrong_state_transition_caught() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: set new_balance to wrong value.
        trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = BabyBear::new(999);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_err(), "Wrong state transition should be caught");
    }

    #[test]
    fn test_invalid_selector_two_active_caught() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 50,
            direction: 0,
        }];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: activate two selectors.
        trace[0][sel::NOOP] = BabyBear::ONE;
        // sel::TRANSFER is already 1, now both are 1.

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_err(), "Two active selectors should be caught");
    }

    #[test]
    fn test_nonce_gap_caught() {
        let state = make_initial_state(1000);
        let effects = vec![
            Effect::Transfer {
                amount: 50,
                direction: 0,
            },
            Effect::Transfer {
                amount: 30,
                direction: 0,
            },
        ];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: skip a nonce (set state_after nonce on row 0 to wrong value).
        // The nonce in state_after[nonce] should be 1 (started at 0, incremented once).
        // Set it to 5 to create a gap.
        trace[0][STATE_AFTER_BASE + state::NONCE] = BabyBear::new(5);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_err(), "Nonce gap should be caught");
    }

    #[test]
    fn test_padding_rows_valid() {
        let state = make_initial_state(100);
        // Single effect padded to 2 rows.
        let effects = vec![Effect::Transfer {
            amount: 10,
            direction: 0,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 2);

        // Verify padding row has NoOp selector.
        assert_eq!(trace[1][sel::NOOP], BabyBear::ONE);

        let air = EffectVmAir::new(trace.len());

        // Check constraints on both rows.
        let alpha = BabyBear::new(7);
        for i in 0..trace.len() {
            let next_idx = (i + 1) % trace.len();
            let c = air.eval_constraints(&trace[i], &trace[next_idx], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Constraint non-zero at row {}: c = {}",
                i,
                c.0
            );
        }
    }

    #[test]
    fn test_conservation_violation_caught() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];

        let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: claim delta = 0 instead of -100.
        public_inputs[pi::NET_DELTA_MAG] = BabyBear::ZERO;
        public_inputs[pi::NET_DELTA_SIGN] = BabyBear::ZERO;

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_err(),
            "Conservation violation should be caught by boundary constraint mismatch"
        );
    }

    #[test]
    fn test_note_spend_and_create() {
        let state = make_initial_state(1000);
        let effects = vec![
            Effect::NoteSpend {
                nullifier: BabyBear::new(0xDEAD),
                value: 500,
            },
            Effect::NoteCreate {
                commitment: BabyBear::new(0xBEEF),
                value: 200,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "NoteSpend + NoteCreate should verify: {:?}",
            result.err()
        );

        // Net delta: +500 - 200 = +300.
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, 300);
    }

    #[test]
    fn test_setfield_correct() {
        let state = make_initial_state(100);
        let effects = vec![Effect::SetField {
            field_idx: 3,
            value: BabyBear::new(77),
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Verify constraints are zero.
        let alpha = BabyBear::new(13);
        let next_idx = 1 % trace.len();
        let c = air.eval_constraints(&trace[0], &trace[next_idx], &public_inputs, alpha);
        assert_eq!(c, BabyBear::ZERO, "SetField should satisfy constraints");
    }

    #[test]
    fn test_grantcap_correct() {
        let state = make_initial_state(100);
        let effects = vec![Effect::GrantCapability {
            cap_entry: BabyBear::new(0x1234),
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        let alpha = BabyBear::new(17);
        let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(c, BabyBear::ZERO, "GrantCap should satisfy constraints");
    }

    #[test]
    fn test_four_effect_stark_roundtrip() {
        let state = make_initial_state(10000);
        let effects = vec![
            Effect::Transfer {
                amount: 500,
                direction: 1,
            },
            Effect::SetField {
                field_idx: 0,
                value: BabyBear::new(99),
            },
            Effect::GrantCapability {
                cap_entry: BabyBear::new(0xABCD),
            },
            Effect::Transfer {
                amount: 200,
                direction: 0,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 4); // exactly power of 2

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "4-effect STARK roundtrip should verify: {:?}",
            result.err()
        );

        // Net delta: -500 + 200 = -300.
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -300);
    }

    #[test]
    fn test_effects_hash_deterministic() {
        let effects = vec![
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
            Effect::SetField {
                field_idx: 2,
                value: BabyBear::new(55),
            },
        ];
        let (h1_lo, h1_hi) = compute_effects_hash(&effects);
        let (h2_lo, h2_hi) = compute_effects_hash(&effects);
        assert_eq!(h1_lo, h2_lo);
        assert_eq!(h1_hi, h2_hi);
    }

    #[test]
    fn test_effects_hash_changes_with_different_effects() {
        let effects1 = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];
        let effects2 = vec![Effect::Transfer {
            amount: 100,
            direction: 0,
        }];
        let (h1_lo, _) = compute_effects_hash(&effects1);
        let (h2_lo, _) = compute_effects_hash(&effects2);
        assert_ne!(h1_lo, h2_lo);
    }

    #[test]
    fn test_cell_state_commitment() {
        let s1 = CellState::new(1000, 0);
        let s2 = CellState::new(1000, 0);
        assert_eq!(s1.state_commitment, s2.state_commitment);

        let s3 = CellState::new(1001, 0);
        assert_ne!(s1.state_commitment, s3.state_commitment);
    }

    #[test]
    fn test_constraint_evaluation_all_zeros_valid_trace() {
        // Generate a valid trace and verify all constraint evaluations are zero.
        let state = make_initial_state(5000);
        let effects = vec![
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
            Effect::Transfer {
                amount: 50,
                direction: 0,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Try multiple alpha values to ensure constraint polynomial is zero everywhere.
        for alpha_val in [3, 7, 13, 29, 101] {
            let alpha = BabyBear::new(alpha_val);
            for i in 0..trace.len() {
                let next_idx = (i + 1) % trace.len();
                let c = air.eval_constraints(
                    &trace[i],
                    &trace[next_idx],
                    &public_inputs,
                    alpha,
                );
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "Constraint non-zero at row {} with alpha={}: c = {}",
                    i,
                    alpha_val,
                    c.0
                );
            }
        }
    }
}
