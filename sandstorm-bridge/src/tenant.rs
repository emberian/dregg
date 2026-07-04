//! **L6 — multi-tenancy.** Grains are isolated from each other; one tenant's grain
//! cannot see, enumerate, or reach another tenant's grain except by an explicit cap.
//!
//! Sandstorm gives this by construction — each grain is its own sandbox, private to
//! its creator, shared only by a powerbox grant; there is no ambient way for grain A
//! to learn that grain B exists. the hosting substrate adds a **tenant partition** above the owner:
//! a grain belongs to a [`TenantId`], and the only cross-grain reach is a cap (which
//! must be powerbox-granted, leaving a receipt). The registry below refuses every
//! ambient cross-tenant operation — enumeration, lookup-by-id, and reach — so a
//! hostile `.spk` cannot discover or touch a neighbour.
//!
//! This complements [`crate::bridge`]'s per-request rule that a session's cap must
//! name the grain it acts on (no ambient authority): L7 stops cross-grain *action*,
//! L6 stops cross-tenant *visibility*.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// A tenant — the isolation partition a grain belongs to. Grains of different tenants
/// are mutually invisible.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TenantId(pub String);

impl TenantId {
    pub fn new(id: impl Into<String>) -> Self {
        TenantId(id.into())
    }
}

/// Why a cross-tenant operation was refused.
#[derive(Debug, PartialEq, Eq)]
pub enum TenantError {
    /// The caller tried to reach/resolve a grain that belongs to another tenant
    /// without holding a cap for it — a cross-tenant breach, refused.
    CrossTenant { caller: TenantId, owner: TenantId },
    /// No grain with that id is visible to the caller (it may not exist, or it belongs
    /// to another tenant — the registry does not distinguish, so absence leaks nothing).
    NotVisible,
}

impl std::fmt::Display for TenantError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TenantError::CrossTenant { caller, owner } => write!(
                f,
                "cross-tenant access refused: tenant {:?} may not reach a grain of tenant {:?}",
                caller.0, owner.0
            ),
            TenantError::NotVisible => write!(f, "grain not visible to this tenant"),
        }
    }
}
impl std::error::Error for TenantError {}

/// A grain's tenancy record in the registry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct GrainEntry {
    tenant: TenantId,
}

/// The grain registry, partitioned by tenant. Every visibility/reach query is made
/// *as a tenant*, and the registry refuses anything outside that tenant's partition
/// (unless an explicit cap is presented, which routes through the powerbox, not here).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct TenantRegistry {
    grains: BTreeMap<String, GrainEntry>,
}

impl TenantRegistry {
    pub fn new() -> Self {
        TenantRegistry::default()
    }

    /// Register a grain as belonging to `tenant`.
    pub fn register(&mut self, grain_cell_id: impl Into<String>, tenant: TenantId) {
        self.grains
            .insert(grain_cell_id.into(), GrainEntry { tenant });
    }

    /// **List** the grains visible to `caller` — *only* that tenant's grains. A hostile
    /// grain cannot enumerate the host's other tenants (no ambient discovery).
    pub fn visible_to(&self, caller: &TenantId) -> Vec<&str> {
        self.grains
            .iter()
            .filter(|(_, e)| &e.tenant == caller)
            .map(|(id, _)| id.as_str())
            .collect()
    }

    /// **Resolve** a grain id as `caller`. Succeeds only if the grain belongs to the
    /// caller's tenant. A cross-tenant id resolves to [`TenantError::NotVisible`] —
    /// the registry will not even confirm the neighbour exists (no existence oracle).
    pub fn resolve<'a>(
        &self,
        caller: &TenantId,
        grain_cell_id: &'a str,
    ) -> Result<&'a str, TenantError> {
        match self.grains.get(grain_cell_id) {
            Some(e) if &e.tenant == caller => Ok(grain_cell_id),
            // Both "belongs to another tenant" and "does not exist" return the same
            // answer, so a probe leaks nothing about the neighbour's existence.
            _ => Err(TenantError::NotVisible),
        }
    }

    /// **Reach** check between two grains: may a grain of `caller` reach
    /// `target_grain` *ambiently* (without a cap)? Only within the same tenant. Across
    /// tenants this is always refused — cross-tenant reach requires a powerbox cap,
    /// which is enforced at the bridge/powerbox, not granted ambiently here.
    pub fn may_reach_ambiently(
        &self,
        caller: &TenantId,
        target_grain: &str,
    ) -> Result<(), TenantError> {
        match self.grains.get(target_grain) {
            Some(e) if &e.tenant == caller => Ok(()),
            Some(e) => Err(TenantError::CrossTenant {
                caller: caller.clone(),
                owner: e.tenant.clone(),
            }),
            None => Err(TenantError::NotVisible),
        }
    }

    pub fn tenant_of(&self, grain_cell_id: &str) -> Option<&TenantId> {
        self.grains.get(grain_cell_id).map(|e| &e.tenant)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn registry() -> (TenantRegistry, TenantId, TenantId) {
        let mut r = TenantRegistry::new();
        let alice = TenantId::new("tenant:alice");
        let bob = TenantId::new("tenant:bob");
        r.register("cell:alice-pad", alice.clone());
        r.register("cell:alice-chat", alice.clone());
        r.register("cell:bob-secret", bob.clone());
        (r, alice, bob)
    }

    #[test]
    fn a_tenant_sees_only_its_own_grains() {
        let (r, alice, _bob) = registry();
        let mut visible = r.visible_to(&alice);
        visible.sort();
        assert_eq!(visible, vec!["cell:alice-chat", "cell:alice-pad"]);
        // Bob's grain is NOT in Alice's view.
        assert!(!visible.contains(&"cell:bob-secret"));
    }

    #[test]
    fn a_cross_tenant_grain_is_not_even_resolvable() {
        let (r, alice, _bob) = registry();
        // Alice cannot resolve Bob's grain — and gets the same NotVisible she'd get for
        // a nonexistent id, so she cannot probe for her neighbours' existence.
        assert_eq!(
            r.resolve(&alice, "cell:bob-secret"),
            Err(TenantError::NotVisible)
        );
        assert_eq!(
            r.resolve(&alice, "cell:does-not-exist"),
            Err(TenantError::NotVisible)
        );
        // Her own grain resolves fine.
        assert_eq!(r.resolve(&alice, "cell:alice-pad"), Ok("cell:alice-pad"));
    }

    #[test]
    fn ambient_cross_tenant_reach_is_refused() {
        let (r, alice, bob) = registry();
        // A hostile grain of Alice's tenant cannot ambiently reach Bob's grain.
        assert_eq!(
            r.may_reach_ambiently(&alice, "cell:bob-secret"),
            Err(TenantError::CrossTenant {
                caller: alice.clone(),
                owner: bob.clone()
            })
        );
        // Same-tenant ambient reach is fine (they share a partition).
        assert!(r.may_reach_ambiently(&alice, "cell:alice-chat").is_ok());
    }
}
