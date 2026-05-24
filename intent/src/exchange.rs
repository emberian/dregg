//! Exchange-specific types for multi-asset ring trade solving.
//!
//! These types extend the intent engine's capability-shaped matching with
//! asset exchange semantics needed for the CoW (Coincidence of Wants) solver.
//!
//! ## Note on the deleted `AssetRegistry`
//!
//! Earlier revisions exported an `AssetRegistry` / `AssetInfo` / `AssetType`
//! triple that classified assets for compatibility. Nothing in the workspace
//! ever consulted it — the asset-only ring solver (`solver.rs`) and the
//! heterogeneous solver (`generalized.rs`) both work directly off the
//! `AssetId` bytes and infer compatibility from per-leg `offer_asset ==
//! want_asset` equality. The registry was dead code (audit §11) and is
//! removed. Asset-type classification, if it returns, should live as
//! per-app metadata on the `GeneralizedExchangeItem::Capability` /
//! `Service` / etc. variants in `generalized.rs`, which already carry
//! richer per-item shape.

/// Asset identifier (content-addressed from token metadata).
pub type AssetId = [u8; 32];
