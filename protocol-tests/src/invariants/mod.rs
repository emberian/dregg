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
