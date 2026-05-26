//! Simulated DFA router for testing route classification and governance updates.
//!
//! Wraps the real `GovernedRouter` from `dregg-dfa` (via the wire re-export)
//! with ergonomic test helpers for building route tables, classifying paths,
//! and proposing governance amendments.

use dregg_wire::dfa_router::{
    GovernanceProof, GovernedRouter, RouteTarget, RouteUpdateError, compile_routes,
};

/// A simulated governed router attached to a federation.
pub struct SimRouter {
    pub router: GovernedRouter,
    pub routes: Vec<(String, RouteTarget)>,
}

impl SimRouter {
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

    /// Classify a path string. Returns a cloned `RouteTarget` if a route matched.
    pub fn classify(&self, path: &str) -> Option<RouteTarget> {
        self.router
            .classify_path(path.as_bytes())
            .map(|c| c.target.clone())
    }

    pub fn classify_bytes(&self, data: &[u8]) -> Option<RouteTarget> {
        self.router.classify(data).map(|c| c.target.clone())
    }

    pub fn commitment(&self) -> [u8; 32] {
        *self.router.commitment()
    }

    pub fn propose_amendment(
        &mut self,
        new_routes: &[(&str, RouteTarget)],
    ) -> Result<[u8; 32], RouteUpdateError> {
        let old_commitment = *self.router.commitment();
        let new_table = compile_routes(new_routes);
        let new_commitment = new_table.commitment;

        let proof = GovernanceProof {
            expected_old_commitment: old_commitment,
            // Stub verifier requires non-empty bytes; in production this is
            // the real threshold-signature payload.
            proof_data: vec![0xAA, 0xBB],
        };

        self.router.update_routes(new_table, &proof)?;

        self.routes = new_routes
            .iter()
            .map(|(p, t)| (p.to_string(), t.clone()))
            .collect();

        Ok(new_commitment)
    }

    pub fn propose_with_wrong_commitment(
        &mut self,
        new_routes: &[(&str, RouteTarget)],
        fake_old_commitment: [u8; 32],
    ) -> Result<[u8; 32], RouteUpdateError> {
        let new_table = compile_routes(new_routes);
        let new_commitment = new_table.commitment;

        let bad_proof = GovernanceProof {
            expected_old_commitment: fake_old_commitment,
            proof_data: vec![0xAA, 0xBB],
        };

        self.router.update_routes(new_table, &bad_proof)?;

        self.routes = new_routes
            .iter()
            .map(|(p, t)| (p.to_string(), t.clone()))
            .collect();

        Ok(new_commitment)
    }

    pub fn has_route(&self, pattern: &str) -> bool {
        self.routes.iter().any(|(p, _)| p == pattern)
    }

    pub fn route_count(&self) -> usize {
        self.routes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_captp::FederationId as GroupId;
    use dregg_types::CellId;

    fn test_cell(n: u8) -> CellId {
        CellId([n; 32])
    }

    #[test]
    fn basic_path_classification() {
        let router = SimRouter::with_routes(&[
            ("/cells/alpha/*", cell_target(test_cell(1))),
            ("/intents/*", RouteTarget::handler("intent_pool")),
            ("/blocked/*", RouteTarget::Drop),
        ]);

        assert_eq!(
            router.classify("/cells/alpha/transfer"),
            Some(cell_target(test_cell(1)))
        );
        assert_eq!(
            router.classify("/intents/submit"),
            Some(RouteTarget::handler("intent_pool"))
        );
        assert_eq!(router.classify("/blocked/evil"), Some(RouteTarget::Drop));
        assert_eq!(router.classify("/unknown/path"), None);
    }

    #[test]
    fn governance_amendment_succeeds() {
        let mut router = SimRouter::with_routes(&[("/cells/alpha/*", cell_target(test_cell(1)))]);

        let old_commitment = router.commitment();

        let new_commitment = router
            .propose_amendment(&[
                ("/cells/alpha/*", cell_target(test_cell(2))),
                ("/cells/beta/*", cell_target(test_cell(3))),
            ])
            .unwrap();

        assert_ne!(old_commitment, new_commitment);
        assert_eq!(
            router.classify("/cells/alpha/x"),
            Some(cell_target(test_cell(2)))
        );
        assert_eq!(
            router.classify("/cells/beta/y"),
            Some(cell_target(test_cell(3)))
        );
    }

    #[test]
    fn governance_amendment_rejects_wrong_commitment() {
        let mut router = SimRouter::with_routes(&[("/cells/alpha/*", cell_target(test_cell(1)))]);

        let result = router.propose_with_wrong_commitment(
            &[("/cells/alpha/*", cell_target(test_cell(2)))],
            [0xFF; 32],
        );

        assert!(result.is_err());
        assert_eq!(
            router.classify("/cells/alpha/x"),
            Some(cell_target(test_cell(1)))
        );
    }

    #[test]
    fn federation_forwarding_route() {
        let fed_id = GroupId([0x42; 32]);
        let router = SimRouter::with_routes(&[("/federated/partner/*", federation_target(fed_id))]);

        assert_eq!(
            router.classify("/federated/partner/sync"),
            Some(federation_target(fed_id))
        );
    }
}
