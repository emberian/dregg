//! **L2 — network isolation** (the critical layer for overlay-expose).
//!
//! A Sandstorm grain runs in an **unshared network namespace**: it has no network
//! interface but loopback, no DNS, and is *forbidden from creating further
//! namespaces*. The only way a grain reaches anything off-box is a Cap'n Proto
//! capability the user handed it through the powerbox — in practice, a **driver
//! grain** (the sanctioned HTTP/API driver) that exposes one external resource as a
//! capability. A fresh grain reaches *nothing*.
//!
//! This module encodes that posture for the dregg overlay, where the threat is
//! sharper: a grain is *reachable on the overlay*. The load-bearing distinction this
//! module makes precise and enforces:
//!
//! - **INBOUND (overlay-expose)** — clients reach the grain's HTTP *through the
//!   cap-gated bridge*. Exposing a grain publishes the **bridge endpoint**, not the
//!   grain's own network access. The grain never receives an overlay handle; it only
//!   ever sees [`crate::bridge::BridgedRequest`]s the bridge chose to deliver. This is
//!   modeled by [`OverlayExposure`].
//! - **OUTBOUND (egress)** — **denied by default** ([`NetworkPolicy::confined`]). A
//!   grain may reach an external destination *only* through an [`OutboundCap`] granted
//!   via the powerbox, naming a **specific** host+port (one service, not "the
//!   internet"). [`NetworkPolicy::check_outbound`] is the gate.
//!
//! The crucial invariant — and a direct test ([`tests::exposed_grain_still_cannot_reach_out`]):
//! **a hostile grain that is reachable on the overlay still cannot itself reach out
//! over the overlay (or anywhere).** Inbound exposure adds *no* outbound authority.
//! The two directions are independent; confusing them is the classic confused-deputy
//! / SSRF hole this layer closes by construction.

use serde::{Deserialize, Serialize};

/// A specific outbound destination a grain is permitted to reach — and *only* this
/// destination. Backed by a powerbox-granted driver capability (the dregg analog of
/// Sandstorm's HTTP-driver grain). There is no wildcard and no "any host" form: a
/// grant always names one service.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OutboundCap {
    /// The exact host this cap authorizes egress to (no globbing).
    pub host: String,
    /// The exact port. `0` means "any port on this host" only if the granting
    /// authority explicitly chose it; the default grant names a concrete port.
    pub port: u16,
}

impl OutboundCap {
    pub fn to(host: impl Into<String>, port: u16) -> Self {
        OutboundCap {
            host: host.into(),
            port,
        }
    }

    fn authorizes(&self, host: &str, port: u16) -> bool {
        self.host == host && (self.port == port || self.port == 0)
    }
}

/// The decision the egress gate returns for an outbound attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EgressDecision {
    /// A granted [`OutboundCap`] authorizes this exact destination.
    Allowed,
    /// No granted cap names this destination — the deny-default (no ambient network).
    DeniedNoCap,
}

impl EgressDecision {
    pub fn is_allowed(self) -> bool {
        matches!(self, EgressDecision::Allowed)
    }
}

/// A grain's network policy. Default ([`confined`](Self::confined)) is the Sandstorm
/// posture: **no ambient network**, no outbound, no DNS, no peer/overlay reach.
/// Outbound is an *allow-list* of powerbox-granted [`OutboundCap`]s; the list starts
/// empty (deny-all) and only the powerbox can add to it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NetworkPolicy {
    /// The allow-list of outbound destinations, each backed by a granted driver cap.
    /// EMPTY = deny-all (a fresh grain reaches nothing).
    granted_outbound: Vec<OutboundCap>,
}

impl Default for NetworkPolicy {
    fn default() -> Self {
        Self::confined()
    }
}

impl NetworkPolicy {
    /// A fully-confined grain: no ambient network, empty outbound allow-list. The
    /// state every grain starts in (Sandstorm's unshared net namespace).
    pub fn confined() -> Self {
        NetworkPolicy {
            granted_outbound: Vec::new(),
        }
    }

    /// Grant outbound reach to one specific service (the powerbox handing the grain a
    /// driver capability). This is the *only* way the allow-list grows.
    pub fn grant_outbound(&mut self, cap: OutboundCap) {
        if !self.granted_outbound.contains(&cap) {
            self.granted_outbound.push(cap);
        }
    }

    /// Revoke a previously-granted outbound cap (the cap-revocation path).
    pub fn revoke_outbound(&mut self, cap: &OutboundCap) {
        self.granted_outbound.retain(|c| c != cap);
    }

    /// The egress gate: may this grain reach `host:port`? Allowed iff a granted
    /// [`OutboundCap`] names exactly that destination; otherwise denied (deny-default).
    pub fn check_outbound(&self, host: &str, port: u16) -> EgressDecision {
        if self
            .granted_outbound
            .iter()
            .any(|c| c.authorizes(host, port))
        {
            EgressDecision::Allowed
        } else {
            EgressDecision::DeniedNoCap
        }
    }

    /// Does the grain have *any* outbound authority at all? A confined grain has none.
    pub fn has_any_egress(&self) -> bool {
        !self.granted_outbound.is_empty()
    }

    pub fn granted(&self) -> &[OutboundCap] {
        &self.granted_outbound
    }
}

/// The **inbound** overlay exposure of a grain. Publishing this makes the grain's HTTP
/// reachable *through the bridge* at `overlay_name` — it does **not** give the grain
/// network access. The grain holds no field of this type; it is the operator/bridge's
/// record of "this grain's bridge endpoint is reachable on the overlay". Constructing
/// one never touches a [`NetworkPolicy`]: inbound exposure confers zero egress.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OverlayExposure {
    /// The overlay name clients use to reach the grain's bridge (the dregg analog of
    /// Sandstorm's per-session wildcard host, e.g. `<name>.dregg.works`).
    pub overlay_name: String,
    /// The grain cell whose bridge is exposed.
    pub grain_cell_id: String,
}

impl OverlayExposure {
    /// Expose a grain's bridge on the overlay. The grain's [`NetworkPolicy`] is *not*
    /// an input and is *not* modified — inbound exposure is orthogonal to egress.
    pub fn expose(overlay_name: impl Into<String>, grain_cell_id: impl Into<String>) -> Self {
        OverlayExposure {
            overlay_name: overlay_name.into(),
            grain_cell_id: grain_cell_id.into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_fresh_grain_reaches_nothing() {
        let net = NetworkPolicy::confined();
        // No ambient network: every outbound attempt is denied.
        assert_eq!(
            net.check_outbound("evil.example.com", 443),
            EgressDecision::DeniedNoCap
        );
        assert_eq!(
            net.check_outbound("127.0.0.1", 8000),
            EgressDecision::DeniedNoCap
        );
        assert_eq!(
            net.check_outbound("metadata.google.internal", 80),
            EgressDecision::DeniedNoCap
        );
        assert!(!net.has_any_egress());
    }

    #[test]
    fn outbound_is_allowed_only_to_the_exact_granted_service() {
        let mut net = NetworkPolicy::confined();
        // The powerbox grants a driver cap to ONE service (api.weather.test:443).
        net.grant_outbound(OutboundCap::to("api.weather.test", 443));

        assert!(net.check_outbound("api.weather.test", 443).is_allowed());
        // A different port on the same host is NOT authorized.
        assert_eq!(
            net.check_outbound("api.weather.test", 80),
            EgressDecision::DeniedNoCap
        );
        // A different host is NOT authorized — no wildcard egress.
        assert_eq!(
            net.check_outbound("evil.example.com", 443),
            EgressDecision::DeniedNoCap
        );
    }

    #[test]
    fn revocation_re_confines_the_grain() {
        let mut net = NetworkPolicy::confined();
        let cap = OutboundCap::to("api.weather.test", 443);
        net.grant_outbound(cap.clone());
        assert!(net.check_outbound("api.weather.test", 443).is_allowed());
        net.revoke_outbound(&cap);
        assert_eq!(
            net.check_outbound("api.weather.test", 443),
            EgressDecision::DeniedNoCap
        );
    }

    #[test]
    fn exposed_grain_still_cannot_reach_out() {
        // THE load-bearing invariant for overlay-expose: a grain reachable INBOUND on
        // the overlay gains NO outbound authority. The two directions are independent.
        let net = NetworkPolicy::confined();
        let exposure = OverlayExposure::expose("notes.dregg.works", "cell:grain1");

        // The grain's bridge is reachable on the overlay...
        assert_eq!(exposure.overlay_name, "notes.dregg.works");
        // ...but the grain itself still reaches nothing — not even the overlay it is
        // exposed on. A hostile .spk cannot pivot inbound-exposure into egress.
        assert!(!net.has_any_egress());
        assert_eq!(
            net.check_outbound("notes.dregg.works", 443),
            EgressDecision::DeniedNoCap
        );
        assert_eq!(
            net.check_outbound("another-grain.dregg.works", 443),
            EgressDecision::DeniedNoCap
        );
    }

    #[test]
    fn granting_egress_does_not_open_a_wildcard() {
        let mut net = NetworkPolicy::confined();
        net.grant_outbound(OutboundCap::to("a.test", 443));
        net.grant_outbound(OutboundCap::to("b.test", 443));
        // Exactly the two named services, nothing adjacent.
        assert!(net.check_outbound("a.test", 443).is_allowed());
        assert!(net.check_outbound("b.test", 443).is_allowed());
        assert_eq!(
            net.check_outbound("c.test", 443),
            EgressDecision::DeniedNoCap
        );
        assert_eq!(net.granted().len(), 2);
    }
}
