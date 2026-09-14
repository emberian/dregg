//! Computron cost configuration for turn metering.

use serde::{Deserialize, Serialize};

/// Cost configuration for computron metering.
///
/// Each operation has a base cost in computrons. The total cost of a turn
/// is the sum of all operation costs. If the agent's fee doesn't cover the
/// total, the turn is rejected.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ComputronCosts {
    /// Base cost per action in the forest.
    pub action_base: u64,
    /// Base cost per effect applied.
    pub effect_base: u64,
    /// Cost per computron transfer.
    pub transfer: u64,
    /// Cost for creating a new cell.
    pub create_cell: u64,
    /// Cost for verifying a ZK proof.
    pub proof_verify: u64,
    /// Cost for verifying a signature.
    pub signature_verify: u64,
    /// Cost per byte of data processed.
    pub per_byte: u64,
    /// Waive the CHARGE for COORDINATION turns
    /// ([`Turn::is_coordination`](crate::turn::Turn::is_coordination):
    /// EmitEvent-only, no `balance_change`) — "leash, not ledger": the
    /// computron is an oversight budget, and coordination turns are the
    /// oversight traffic itself. Opt-in, default `false` = exact legacy
    /// behavior; `#[serde(default)]` keeps persisted/wire cost configs
    /// compatible. When enabled, a `fee = 0` coordination turn admits and
    /// commits; metering stays honest (receipts still report the true
    /// `computrons_used` — only the admission charge is waived) and economic
    /// turns (Transfer/Burn/NoteSpend/CreateCell/SetField/…) charge exactly
    /// as before.
    #[serde(default)]
    pub coordination_exempt: bool,
}

impl ComputronCosts {
    /// Default cost configuration (reasonable for testing).
    pub fn default_costs() -> Self {
        ComputronCosts {
            action_base: 100,
            effect_base: 50,
            transfer: 75,
            create_cell: 500,
            proof_verify: 1000,
            signature_verify: 200,
            per_byte: 1,
            coordination_exempt: false,
        }
    }

    /// Zero costs (for testing without metering).
    pub fn zero() -> Self {
        ComputronCosts {
            action_base: 0,
            effect_base: 0,
            transfer: 0,
            create_cell: 0,
            proof_verify: 0,
            signature_verify: 0,
            per_byte: 0,
            coordination_exempt: false,
        }
    }
}

impl Default for ComputronCosts {
    fn default() -> Self {
        Self::default_costs()
    }
}
