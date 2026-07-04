//! # sandstorm-bridge — the dregg-native Sandstorm integration, made executable
//!
//! Running [Sandstorm.io](https://sandstorm.org) apps as dregg cells on the hosting
//! substrate. The crate models the keystone mappings as plain Rust + tests, so the
//! design is *exercised* (with real `.spk` crypto) end to end:
//!
//! 1. [`spk`] — read a **real `.spk` package**: the 8-byte magic, real **xz**
//!    decompression, the **Ed25519** signature over the archive (the App ID *is* the
//!    signing key), and the Cap'n Proto `Archive` (the chroot tree). A tampered or
//!    mis-signed package never yields a launchable image.
//! 2. [`manifest`] — decode the [`manifest::SpkManifest`] out of the `.spk` and
//!    derive the [`grain::GrainSpec`] (entry command + sandbox demand) it implies.
//! 3. [`cell`] — the grain's `/var` = a dregg cell's **umem heap**, committing to a
//!    content-addressed [`cell::DataRoot`] (a re-witnessable checkpoint).
//! 4. [`grain`] — a **grain = a dregg cell + a cap-bounded workload**: the lifecycle
//!    (create / wake / sleep / delete) over dregg's lease + durable + umem.
//! 5. [`bridge`] — the **dregg http-bridge shim**: the `WebSession` HTTP surface, the
//!    `X-Sandstorm-*` identity/permission headers **derived from the holder's dregg
//!    cap**, and the grain `/var` ↔ cell umem wiring. Run a catalog app and serve it.
//! 6. [`webauth_rail`] — Sandstorm's **powerbox** = dregg's attenuable caps: a grain
//!    capability is a real [`dregg_auth::credential::Credential`] (`dga1_…`, ed25519
//!    caveat-chain, host-rooted, attenuating-only), minted/attenuated/read on the
//!    real rail.
//!
//! Two operated-layer welds present upstream are out of scope here (a named
//! follow-up): the compute-tier `exec_workload` weld (onto the sandbox executor)
//! and the `serving` weld (onto the hosting substrate's site-serving surface).
//! Both bind operated-execution / site-serving crates that are not breadstuffs
//! siblings; the confinement + capability model below stands complete without them.
//!
//! The point: the mapping is *structural*, not a shim — Sandstorm and dregg are the
//! same object-capability discipline, and dregg adds the half Sandstorm lacks (a
//! light client can *witness* the delegation and the served bytes, not just trust the
//! supervisor to enforce them).

//! ## Defense-in-depth (a malicious `.spk` on the overlay)
//!
//! Because grains run untrusted third-party `.spk` apps and are exposed on the dregg
//! overlay, the crate also realizes the independent containment layers documented in
//! `../docs/SANDSTORM-DEFENSE-IN-DEPTH.md`:
//!
//! - **L2 network isolation** ([`net`]) — a grain has no ambient network; outbound is
//!   deny-default and only via a powerbox-granted [`net::OutboundCap`]; overlay-expose
//!   is inbound-through-the-bridge-only and confers zero egress.
//! - **L4 resource bounds** ([`limits`]) — the funded lease bounds uptime/CPU/memory/
//!   storage; a grain that outruns it is refused/reaped.
//! - **L6 multi-tenancy** ([`tenant`]) — grains are partitioned by [`tenant::TenantId`];
//!   a tenant cannot enumerate, resolve, or ambiently reach another's grain.
//! - **L7 the bridge choke** ([`bridge`]) — all grain I/O (inbound serve + outbound
//!   egress) flows through the cap-gated bridge; nothing bypasses it.

pub mod bridge;
pub mod capnp_wire;
pub mod cell;
pub mod grain;
pub mod limits;
pub mod manifest;
pub mod net;
pub mod spk;
pub mod tenant;
pub mod webauth_rail;

pub use bridge::{
    BridgedRequest, GrainWorkload, HttpBridge, HttpRequest, HttpResponse, Method, NotesApp, Served,
    Session,
};
pub use cell::{DataRoot, Umem};
pub use grain::{
    restore_grain, GrainBackup, GrainCell, GrainError, GrainReceipt, GrainSpec, GrainState,
    SandboxTier, IDLE_SHUTDOWN_SECS,
};
pub use limits::{LeaseError, ResourceKind, ResourceLease};
pub use manifest::{AppId, SpkManifest};
pub use net::{EgressDecision, NetworkPolicy, OutboundCap, OverlayExposure};
pub use spk::{Archive, File, FileContent, Spk, SpkBuilder, SpkError};
pub use tenant::{TenantError, TenantId, TenantRegistry};

// --- the powerbox cap rail (minted / attenuated / read on the real dregg-auth rail) ---
pub use webauth_rail::{attenuate_grain_cap, derive_permissions, HostAuthority};

#[cfg(test)]
mod integration_tests {
    //! End-to-end: install a (synthetic, genuinely-signed) `.spk` → derive the grain
    //! spec → create a grain cell → wake under a funded lease → serve a request
    //! through the http-bridge shim (cap-derived permissions) → meter uptime → sleep
    //! (checkpoint the umem) → wake → prove the grain state survived. This is the
    //! safe-autonomous "fixture `.spk` → live grain session" path the plan §9 names.

    use crate::bridge::{HttpBridge, HttpRequest, NotesApp, Session};
    use crate::cell::Umem;
    use crate::grain::{GrainCell, GrainState, SandboxTier};
    use crate::manifest::SpkManifest;
    use crate::spk::{test_signing_key, File, Spk, SpkBuilder};
    use crate::webauth_rail::HostAuthority;

    /// The host's powerbox root — caps presented to the bridge chain back to it.
    fn host_authority() -> HostAuthority {
        HostAuthority::from_seed([42u8; 32])
    }

    fn declared() -> Vec<String> {
        vec!["view".into(), "edit".into()]
    }

    fn etherpad_spk() -> Vec<u8> {
        let manifest = r#"{
          "app_id": "overridden-by-the-signing-key",
          "app_title": "Etherpad",
          "app_version": 33,
          "marketing_version": "1.8.18",
          "continue_command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/start.sh"] },
          "bridge_config": {
            "api_port": 8000,
            "permissions": ["view", "edit"],
            "roles": [
              { "title": "editor", "permissions": ["view", "edit"] },
              { "title": "viewer", "permissions": ["view"] }
            ]
          }
        }"#;
        SpkBuilder::new()
            .manifest_json(manifest)
            .file(File::executable("start.sh", b"#!/bin/sh\n".to_vec()))
            .pack(&test_signing_key())
    }

    #[test]
    fn install_spk_then_run_grain_and_persist() {
        // 1. Install: parse + verify the .spk, decode the manifest, derive the spec.
        let spk = Spk::parse(&etherpad_spk()).expect("verified .spk");
        let manifest = SpkManifest::from_spk(&spk).expect("manifest from spk");
        assert_eq!(manifest.app_title, "Etherpad");
        // The App ID came from the signing key, not the manifest body.
        assert_eq!(manifest.app_id, spk.app_id());
        let spec = manifest.grain_spec();
        // An http-bridge app routes to the Caged jail (never weaker).
        assert_eq!(spec.tier, SandboxTier::Caged);
        assert_eq!(spec.ingress_port, Some(8000));

        // 2. Create the grain cell.
        let grain_id = "cell:etherpad-grain-1";
        let mut grain = GrainCell::create(grain_id, "user:alice", spec);
        assert_eq!(grain.state, GrainState::Created);

        // 3. Wake under a funded lease (an unfunded lease would refuse).
        grain.wake(true).expect("funded wake");
        assert_eq!(grain.state, GrainState::Running);

        // 4. Serve a request through the http-bridge shim. Alice holds an editor cap
        //    over the grain (a real dga1_ credential, host-rooted, sealed to her);
        //    the facets it grants become X-Sandstorm-Permissions.
        let host = host_authority();
        let mut var = Umem::new();
        let alice_token = host
            .mint_grain_cap(grain_id, "u:alice", &["view", "edit"], None)
            .encode();
        let alice = Session::presenting("u:alice", "alice", "s:1", alice_token, "u:alice");
        let served = HttpBridge::serve(
            &NotesApp,
            grain_id,
            &alice,
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::post("/pad/welcome", b"hello dregg".to_vec()),
        );
        assert_eq!(served.response.status, 200);

        // 5. Meter uptime (a StandingObligation tick), then sleep: checkpoint the umem
        //    into the grain's committed data_root.
        grain.meter_period(1).unwrap();
        grain.sleep(served.new_data_root.clone()).unwrap();
        assert_eq!(grain.state, GrainState::Sleeping);
        let checkpoint = grain.data_root.clone().unwrap();

        // 6. Wake again and prove the grain state survived the checkpoint: a viewer
        //    reads the note back through the bridge from the restored umem.
        grain.wake(true).unwrap();
        assert_eq!(grain.data_root.as_deref(), Some(checkpoint.as_str()));
        let bob_token = host
            .mint_grain_cap(grain_id, "u:bob", &["view"], None)
            .encode();
        let bob = Session::presenting("u:bob", "bob", "s:2", bob_token, "u:bob");
        let read = HttpBridge::serve(
            &NotesApp,
            grain_id,
            &bob,
            &host.public(),
            &declared(),
            1000,
            &mut var, // the same restored umem the checkpoint committed to
            &HttpRequest::get("/pad/welcome"),
        );
        assert_eq!(read.response.status, 200);
        assert_eq!(read.response.body, b"hello dregg");
        // And the read of the restored umem commits to the same checkpoint root.
        assert_eq!(read.new_data_root.0, checkpoint);
    }

    /// Defense-in-depth: a **fully-malicious** grain, sandboxed and reachable on the
    /// overlay, attempts each threat in turn — every one is REFUSED by an independent
    /// layer (see `../docs/SANDSTORM-DEFENSE-IN-DEPTH.md`). The grain's code is assumed
    /// hostile; these are the layers that hold regardless.
    #[test]
    fn a_hostile_grain_is_refused_at_every_layer() {
        use crate::bridge::{HttpBridge, HttpRequest};
        use crate::grain::{GrainCell, GrainError};
        use crate::limits::ResourceLease;
        use crate::manifest::SpkManifest;
        use crate::net::{NetworkPolicy, OutboundCap, OverlayExposure};
        use crate::spk::Spk;
        use crate::tenant::{TenantError, TenantId, TenantRegistry};

        // Install the (genuinely-signed) app; the signature gates the image (L1 root).
        let spk = Spk::parse(&etherpad_spk()).expect("verified .spk");
        let spec = SpkManifest::from_spk(&spk).unwrap().grain_spec();

        // The hostile grain belongs to the attacker tenant; a victim grain is a
        // neighbour in another tenant. The grain runs under a tight funded lease.
        let attacker = TenantId::new("tenant:mallory");
        let victim = TenantId::new("tenant:victim");
        let grain_id = "cell:mallory-grain";
        let mut grain = GrainCell::create(grain_id, "user:mallory", spec)
            .with_tenant(attacker.clone())
            .with_lease(ResourceLease::bounded(2, 1000, 64 * 1024 * 1024, 16));
        grain.wake(true).unwrap();

        let mut registry = TenantRegistry::new();
        registry.register(grain_id, attacker.clone());
        registry.register("cell:victim-secret", victim.clone());

        // The grain IS exposed inbound on the overlay (overlay-expose confirmed).
        let _exposure = OverlayExposure::expose("mallory.dregg.works", grain_id);

        // THREAT: reach the network / internet / a metadata endpoint.
        //   L2 — no ambient network; deny-default; not even the overlay it sits on.
        assert!(!HttpBridge::egress(&grain.network, "169.254.169.254", 80).is_allowed());
        assert!(!HttpBridge::egress(&grain.network, "mallory.dregg.works", 443).is_allowed());
        assert!(!HttpBridge::egress(&grain.network, "exfil.evil.test", 443).is_allowed());

        // THREAT: gain authority beyond its caps / reach another grain.
        //   L7 — a cap for another grain is inert at the bridge (no ambient authority).
        //   Even a *genuinely host-rooted* cap over the victim grain (which mallory may
        //   legitimately hold) confers nothing here: the `grain` caveat does not match.
        let host = host_authority();
        let cross_token = host
            .mint_grain_cap("cell:victim-secret", "u:mallory", &["view", "edit"], None)
            .encode();
        let cross = Session::presenting("u:mallory", "mallory", "s:x", cross_token, "u:mallory");
        let mut var = Umem::new();
        let blocked = HttpBridge::serve(
            &NotesApp,
            grain_id,
            &cross,
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::get("/steal"),
        );
        assert_eq!(blocked.response.status, 403);

        //   L7 — and a *forged* cap (not rooted at this host) over the grain itself is
        //   refused outright: the ed25519 chain verify fails.
        let forged_over_self = {
            let attacker = HostAuthority::from_seed([66u8; 32]);
            let token = attacker
                .mint_grain_cap(grain_id, "u:mallory", &["view", "edit"], None)
                .encode();
            Session::presenting("u:mallory", "mallory", "s:f", token, "u:mallory")
        };
        let forged_blocked = HttpBridge::serve(
            &NotesApp,
            grain_id,
            &forged_over_self,
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::post("/pwn", b"x".to_vec()),
        );
        assert_eq!(forged_blocked.response.status, 403);
        assert!(var.is_empty());

        // THREAT: see / enumerate another tenant's grain.
        //   L6 — cross-tenant is invisible and unresolvable.
        assert!(!registry
            .visible_to(&attacker)
            .contains(&"cell:victim-secret"));
        assert_eq!(
            registry.resolve(&attacker, "cell:victim-secret"),
            Err(TenantError::NotVisible)
        );
        assert!(matches!(
            registry.may_reach_ambiently(&attacker, "cell:victim-secret"),
            Err(TenantError::CrossTenant { .. })
        ));

        // THREAT: exhaust host storage (DoS).
        //   L4 — a write past the 16-byte quota is rolled back (507), nothing persists.
        let bomb_token = host
            .mint_grain_cap(grain_id, "u:mallory", &["view", "edit"], None)
            .encode();
        let bomb = HttpBridge::serve_bounded(
            &NotesApp,
            grain_id,
            &Session::presenting("u:mallory", "mallory", "s:b", bomb_token, "u:mallory"),
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &mut grain.lease,
            &HttpRequest::post("/bomb", vec![0u8; 4096]),
        );
        assert_eq!(bomb.response.status, 507);
        assert!(var.is_empty());

        // THREAT: run unmetered (DoS).
        //   L4 — uptime is bounded by the funded lease; the grain is reaped.
        assert_eq!(grain.meter_period(1).unwrap(), 1);
        assert_eq!(grain.meter_period(1).unwrap(), 2);
        assert!(matches!(
            grain.meter_period(1),
            Err(GrainError::LeaseExhausted(_))
        ));

        // The one sanctioned path still works: the powerbox grants egress to ONE
        // service, and only that destination opens — no wildcard, no pivot.
        let mut policy = NetworkPolicy::confined();
        policy.grant_outbound(OutboundCap::to("api.allowed.test", 443));
        assert!(HttpBridge::egress(&policy, "api.allowed.test", 443).is_allowed());
        assert!(!HttpBridge::egress(&policy, "api.allowed.test", 8443).is_allowed());
    }
}
