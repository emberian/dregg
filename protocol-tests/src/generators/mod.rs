//! Proptest strategies for generating *valid-shaped* protocol inputs.
//!
//! "Valid-shaped" means: the executor will accept this at parse time and
//! actually exercise the property under test. We deliberately do NOT
//! generate garbage that bounces off rejection paths — that just tests the
//! parser, not the invariant.
//!
//! Each strategy is parameterised by a `LedgerSpec` describing the ambient
//! cell-set the inputs reference, so that turn-shaped inputs target cells
//! that actually exist with permissions/capabilities the executor will
//! honour.

pub mod cell;
pub mod capability;
pub mod effect;
pub mod turn;

pub use cell::{LedgerSpec, build_open_ledger};
pub use turn::{
    TransferOp, arb_transfer_op, arb_transfer_ops, build_no_op_turn, build_transfer_turn,
};
