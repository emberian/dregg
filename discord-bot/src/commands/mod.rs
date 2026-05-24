//! Slash command modules.
//!
//! The bot's command surface was trimmed in the post-relocation cleanup:
//! commands that depended on apps deleted from the workspace (the AMM
//! `defi.rs`, the orderbook `orderbook.rs`, and the standalone
//! stablecoin/lending/dao-treasury/prediction-market surfaces) were
//! retired rather than degraded to placeholders. The remaining commands
//! either route to apps still in the workspace (gallery, identity,
//! governed-namespace, nameservice) or to bot-local features (presence,
//! captp, queue, federation, wallet, transfer, status, social).

pub mod explorer;
pub mod gallery;
pub mod identity;
pub mod presence;
pub mod social;
pub mod status;
pub mod transfer;
pub mod wallet;

// ─── CapTP integration commands ─────────────────────────────────────────────
pub mod captp;
pub mod federation;
pub mod governance;
pub mod names;
pub mod queue;
