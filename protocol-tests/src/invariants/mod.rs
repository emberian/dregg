//! Protocol invariant property-test modules.
//!
//! Each submodule owns one invariant from `dev-philosophy/02-testing.md`.
//! The submodules are independent — they share generators but not state —
//! so they can be developed, debugged, and shrunk in isolation.
//!
//! Module status (see `lib.rs` for the canonical list):
//!
//! | Module                       | Status      |
//! |------------------------------|-------------|
//! | `balance_conservation`       | implemented |
//! | `nonce_monotonicity`         | implemented |
//! | `receipt_chain`              | implemented |
//! | `capability_attenuation`     | stub        |
//! | `facet_attenuation`          | stub        |
//! | `sealed_field_integrity`     | stub        |
//! | `permission_enforcement`     | stub        |

pub mod balance_conservation;
pub mod capability_attenuation;
pub mod effect_vm_differential;
pub mod facet_attenuation;
pub mod nonce_monotonicity;
pub mod permission_enforcement;
pub mod receipt_chain;
pub mod sealed_field_integrity;

// New invariants for the substrate-test mandate (silver-vision).
// Each module is one protocol claim from CAVEAT-LAYER-COVERAGE.md,
// SLOT-CAVEATS-DESIGN.md, STAGE-7-GAMMA-2-PI-DESIGN.md, or
// EXECUTOR-HONESTY-AUDIT.md.

/// `Predicate(Vec<_>)` is a conjunction — every constraint must hold.
/// Across randomized inputs, if any conjunct fails the program must reject.
pub mod state_constraint_conjunction;

/// `AnyOf` is a disjunction restricted to `SimpleStateConstraint`. Across
/// randomized inputs: program accepts iff at least one variant holds.
pub mod any_of_disjunction;

/// Sentinel-rejected `StateConstraint` variants (`TemporalPredicate`,
/// `BoundDelta`, `Witnessed`, `Custom`) must bubble up as
/// `TurnError::ProgramViolation` until the caveat-correctness lane lands.
pub mod sentinel_variants_reject;

/// γ.2 canonical id derivations are injective in their preimage components
/// (CAVEAT-LAYER-COVERAGE composition row + STAGE-7-GAMMA-2-PI-DESIGN.md §3).
pub mod gamma2_id_injectivity;

/// Action-hash domain separation across `Authorization` variants — every
/// tamper must change the action hash.
pub mod authorization_hash_domain_separation;

/// 4-phase `BridgeReceiptEnvelope` phase log monotonicity:
/// Locked→Witnessed→Finalized or Locked→Refunded; everything else
/// must reject.
pub mod bridge_phase_monotonicity;

/// γ.2 cross-federation extension: `intro_id` and `transfer_id`
/// preimages must include federation_id when crossing federations (per
/// AUDIT-federation.md F1 + STAGE-7-GAMMA-2-PI-DESIGN §1.3 tail).
pub mod gamma2_cross_federation_binding;
