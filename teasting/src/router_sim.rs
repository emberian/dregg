//! Simulated DFA router for testing route classification and governance updates.
//!
//! Wraps the real `GovernedRouter` from `pyana-wire` with ergonomic test helpers
//! for building route tables, classifying paths, and proposing governance amendments.

use pyana_wire::dfa_router::{
    GovernanceProof, GovernedRouter, RouteTarget, RouteUpdateError, compile_routes,
};

/// A simulated governed router attached to a federation.
///
/// Provides ergonomic test methods around the real `GovernedRouter` for building
/// route tables, classifying paths, and simulating governance-controlled route updates.
pub struct SimRouter {
    /// The inner governed router (real implementation from pyana-wire).
    pub router: GovernedRouter,
    /// The route patterns used to build the current table (for inspection/rebuild).
    pub routes: Vec<(String, RouteTarget)>,
}

impl SimRouter {
    /// Create a new simulated router with the given route patterns.
    ///
    /// # Pattern syntax
    ///
    /// - `/cells/alpha/*` — wildcard match on any continuation after the prefix
    /// - `/admin` — exact match only
    ///
    /// # Example
    ///
    /// ```ignore
    /// let router = SimRouter::with_routes(&[
    ///     ("/cells/stablecoin/*", RouteTarget::Cell(cell_id)),
    ///     ("/intents/*", RouteTarget::Handler("intent_pool".into())),
    /// ]);
    /// ```
    pub fn with_routes(routes: &[(&str, RouteTarget)]) -> Self {
        let table = compile_routes(routes);
        let owned_routes: Vec<(String, RouteTarget)> = routes
            .iter()
            .map(|(p, t)| (p.to_string(), t.clone()))
            .collect();
        Self {
            router: GovernedRouter::new(table),
            routes: owned_routes,
        }
    }

    /// Classify a path string against the current route table.
    ///
    /// Returns the matching `RouteTarget` if found, or `None` if no route matches.
    pub fn classify(&self, path: &str) -> Option<&RouteTarget> {
        self.router.classify_path(path.as_bytes())
    }

    /// Classify raw bytes (e.g., a wire message prefix) against the route table.
    pub fn classify_bytes(&self, data: &[u8]) -> Option<&RouteTarget> {
        self.router.classify(data)
    }

    /// Get the current governance commitment hash.
    pub fn commitment(&self) -> [u8; 32] {
        *self.router.commitment()
    }

    /// Propose a route amendment (governance-controlled update).
    ///
    /// Compiles the new routes into a DFA, then attempts to atomically swap the
    /// route table using compare-and-swap semantics. On success, returns the new
    /// commitment hash. On failure (commitment mismatch), returns the error.
    ///
    /// This simulates a governance proposal being applied: in production, the
    /// GovernanceProof would carry a threshold signature or ZK proof.
    pub fn propose_amendment(
        &mut self,
        new_routes: &[(&str, RouteTarget)],
    ) -> Result<[u8; 32], RouteUpdateError> {
        let old_commitment = *self.router.commitment();
        let new_table = compile_routes(new_routes);
        let new_commitment = new_table.commitment;

        let proof = GovernanceProof {
            expected_old_commitment: old_commitment,
            proof_data: vec![], // placeholder
        };

        self.router.update_routes(new_table, &proof)?;

        // Update stored routes
        self.routes = new_routes
            .iter()
            .map(|(p, t)| (p.to_string(), t.clone()))
            .collect();

        Ok(new_commitment)
    }

    /// Attempt a route update with an explicitly wrong commitment (for testing rejection).
    pub fn propose_with_wrong_commitment(
        &mut self,
        new_routes: &[(&str, RouteTarget)],
        fake_old_commitment: [u8; 32],
    ) -> Result<[u8; 32], RouteUpdateError> {
        let new_table = compile_routes(new_routes);
        let new_commitment = new_table.commitment;

        let bad_proof = GovernanceProof {
            expected_old_commitment: fake_old_commitment,
            proof_data: vec![],
        };

        self.router.update_routes(new_table, &bad_proof)?;

        self.routes = new_routes
            .iter()
            .map(|(p, t)| (p.to_string(), t.clone()))
            .collect();

        Ok(new_commitment)
    }

    /// Check whether a specific route pattern exists in the current table.
    pub fn has_route(&self, pattern: &str) -> bool {
        self.routes.iter().any(|(p, _)| p == pattern)
    }

    /// Get the number of route patterns in the current table.
    pub fn route_count(&self) -> usize {
        self.routes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_captp::FederationId;
    use pyana_types::CellId;

    fn test_cell(n: u8) -> CellId {
        CellId([n; 32])
    }

    #[test]
    fn basic_path_classification() {
        let router = SimRouter::with_routes(&[
            ("/cells/alpha/*", RouteTarget::Cell(test_cell(1))),
            ("/intents/*", RouteTarget::Handler("intent_pool".into())),
            ("/blocked/*", RouteTarget::Drop),
        ]);

        assert_eq!(
            router.classify("/cells/alpha/transfer"),
            Some(&RouteTarget::Cell(test_cell(1)))
        );
        assert_eq!(
            router.classify("/intents/submit"),
            Some(&RouteTarget::Handler("intent_pool".into()))
        );
        assert_eq!(router.classify("/blocked/evil"), Some(&RouteTarget::Drop));
        assert_eq!(router.classify("/unknown/path"), None);
    }

    #[test]
    fn governance_amendment_succeeds() {
        let mut router =
            SimRouter::with_routes(&[("/cells/alpha/*", RouteTarget::Cell(test_cell(1)))]);

        let old_commitment = router.commitment();

        let new_commitment = router
            .propose_amendment(&[
                ("/cells/alpha/*", RouteTarget::Cell(test_cell(2))),
                ("/cells/beta/*", RouteTarget::Cell(test_cell(3))),
            ])
            .unwrap();

        assert_ne!(old_commitment, new_commitment);
        assert_eq!(
            router.classify("/cells/alpha/x"),
            Some(&RouteTarget::Cell(test_cell(2)))
        );
        assert_eq!(
            router.classify("/cells/beta/y"),
            Some(&RouteTarget::Cell(test_cell(3)))
        );
    }

    #[test]
    fn governance_amendment_rejects_wrong_commitment() {
        let mut router =
            SimRouter::with_routes(&[("/cells/alpha/*", RouteTarget::Cell(test_cell(1)))]);

        let result = router.propose_with_wrong_commitment(
            &[("/cells/alpha/*", RouteTarget::Cell(test_cell(2)))],
            [0xFF; 32],
        );

        assert!(result.is_err());
        // Original route unchanged
        assert_eq!(
            router.classify("/cells/alpha/x"),
            Some(&RouteTarget::Cell(test_cell(1)))
        );
    }

    #[test]
    fn federation_forwarding_route() {
        let fed_id = FederationId([0x42; 32]);
        let router =
            SimRouter::with_routes(&[("/federated/partner/*", RouteTarget::Federation(fed_id))]);

        assert_eq!(
            router.classify("/federated/partner/sync"),
            Some(&RouteTarget::Federation(fed_id))
        );
    }
}
