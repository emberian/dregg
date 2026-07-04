//! # grain-commons — the agent commons / grain app-store
//!
//! Package, publish, discover, and fork hosted-agent **grains**: the "app store for
//! hostable / shareable / forkable / pedigreed agents" of docs/THE-GRAIN.md (face #3,
//! §Commons). The design principle is **compose, don't reimplement** — every load-bearing
//! guarantee here is an existing, proven dregg primitive, wired into a market shape:
//!
//! | Commons capability          | Composed primitive                                                        |
//! |-----------------------------|---------------------------------------------------------------------------|
//! | [`package`] — sign & install| `sandstorm_bridge::{SpkBuilder, Spk, SpkManifest}` (App ID = signing key)  |
//! | [`registry`] — the market   | `sandstorm_bridge::{Umem, DataRoot}` listing cells + `GrainReceipt` reviews|
//! | [`fork`] — pedigree         | `sandstorm_bridge::grain::{GrainBackup, restore_grain}` (re-witnessed root)|
//! | [`hatchery`] — genesis-agent| `dregg_sdk::hatchery_mint::MintedKind` + the `dga1_` powerbox cap rail      |
//!
//! The four faces of the commons:
//!
//! 1. **Package an agent** ([`publish`] / [`install`]) — an [`AgentConfig`] (cap bundle +
//!    budget + brain + roles) packaged as a signed `.spk`. **Provenance is the key**: the
//!    App ID is the author's Ed25519 signing key, and a tampered package yields no
//!    installable grain.
//! 2. **List & rent** ([`GrainRegistry`]) — a listing is a **cell** (author key, `.spk`
//!    hash, price/listing terms, invariant digests) in a committed umem heap; discover by
//!    App ID, rent = a priced [`RentQuote`] whose numbers feed the REAL funded lease
//!    (`hosted-lease` / `grain-fork::Grain::rent` — the honest stand-in line, see
//!    `registry`'s module docs), review = a receipted turn.
//! 3. **Fork with pedigree** ([`fork_from_package`]) — fork an installed grain's committed
//!    image into a fresh grain under a new owner, with a [`Pedigree`] Merkle path tracing
//!    it to its author and every fork point.
//! 4. **Hatch bounded sub-agents** ([`GenesisAgent`]) — a genesis-agent mints sub-agents
//!    whose forever-invariant the executor enforces for the child's whole life, endowed
//!    with a strict attenuation of its own caps.

pub mod fork;
pub mod hatchery;
pub mod package;
pub mod registry;

pub use fork::{fork_from_package, ForkError, ForkPoint, ForkedGrain, Pedigree};
pub use hatchery::{GenesisAgent, HatchError, HatchedSubAgent, HpresProof, Invariant, MintedKind};
pub use package::{
    install, publish, AgentBudget, AgentConfig, AgentRole, BrainChoice, GrainPackage, PackageError,
};
pub use registry::{GrainListing, GrainRegistry, ListingTerms, RegistryError, RentQuote, Review};

#[cfg(test)]
mod commons_e2e {
    //! End-to-end: author → package → list → rent → hatch a bounded sub-agent → fork
    //! with pedigree. The whole commons loop over the composed primitives.

    use super::*;
    use ed25519_dalek::SigningKey;
    use sandstorm_bridge::grain::GrainCell;
    use sandstorm_bridge::Umem;

    #[test]
    fn the_full_commons_loop() {
        // ── 1. Author packages an agent and signs it (provenance = the key). ──
        let cfg = AgentConfig::new(
            "Docs Summarizer",
            ["web.fetch", "web.search", "notes.write"],
            AgentBudget {
                max_spend: 5_000,
                max_tool_calls: 200,
            },
            BrainChoice::Llm {
                model: "claude-opus-4-8".into(),
            },
        )
        .with_role("reader", ["web.fetch", "web.search"]);
        let author = SigningKey::from_bytes(&[7u8; 32]);
        let spk = publish(&cfg, &author).unwrap();

        // Anyone installs it and verifies provenance from the signature alone.
        let pkg = install(&spk).unwrap();
        assert_eq!(pkg.config, cfg);

        // ── 2. A genesis-agent hatches a bounded sub-agent of this design. ──
        let genesis = GenesisAgent::new(
            "cell:genesis",
            [7u8; 32],
            [42u8; 32],
            cfg.cap_facets.clone(),
        );
        let sub = genesis
            .mint_subagent(
                "cell:sub-summarizer",
                "u:sub",
                Invariant::MonotoneField { slot: 1 }, // e.g. a monotone call counter
                ["web.fetch", "web.search"],          // strictly fewer than the parent
            )
            .unwrap();
        assert!(sub.is_strict_attenuation());
        // The sub-agent's caps are cryptographically the attenuated set (rail-verified).
        let mut perms = genesis.granted_permissions(&sub, 1_000);
        perms.sort();
        assert_eq!(
            perms,
            vec!["web.fetch".to_string(), "web.search".to_string()]
        );

        // ── 3. List the agent in the registry, pinning the hatched invariant digest. ──
        let mut market = GrainRegistry::new();
        let listing = GrainListing::new(
            pkg.app_id.clone(),
            pkg.spk_hash,
            pkg.config.title.clone(),
            ListingTerms {
                rent_per_period: 100,
                deposit: 250,
                max_periods: 30,
            },
            vec![sub.kind_id()],
        );
        market.publish(listing).unwrap();

        // A renter discovers it by App ID and gets a priced rent quote (the numbers
        // that feed the REAL lease open — grain-fork's Grain::rent).
        let found = market.discover(&pkg.app_id).expect("listed");
        assert_eq!(found.invariant_digests, vec![sub.kind_id()]);
        let quote = market.rent(&pkg.app_id, "user:renter", 4).unwrap();
        assert_eq!(quote.total_cost, 250 + 100 * 4);
        // And leaves a receipted review.
        let receipt = market
            .review(&pkg.app_id, "user:renter", 5, [3u8; 32])
            .unwrap();
        assert_eq!(receipt.op, "review");
        assert_eq!(
            market.discover(&pkg.app_id).unwrap().average_rating(),
            Some(5.0)
        );

        // ── 4. The renter runs the grain, then forks it — pedigree intact. ──
        let mut var = Umem::new();
        var.put(
            "memory/summary",
            b"the docs say: compose, do not reimplement".to_vec(),
        );
        // The renter's identity key attests the backup; the friend's key owns the fork.
        let renter_key = SigningKey::from_bytes(&[55u8; 32]);
        let friend_key = SigningKey::from_bytes(&[56u8; 32]);
        let grain = GrainCell::create("cell:run", "user:renter", pkg.grain_spec());
        let (backup, _) = grain.backup("user:renter", &renter_key, &var).unwrap();

        // The fork verifies the backup's owner attestation against the renter's pubkey
        // (the expected source-grain owner) — all three pedigree teeth bite.
        let forked = fork_from_package(
            &pkg,
            &backup,
            "user:friend",
            &friend_key,
            "cell:forked",
            &renter_key.verifying_key(),
        )
        .unwrap();
        // Provenance traces all the way back to the author's signing key.
        assert!(forked.pedigree.traces_to(&pkg.app_id));
        assert_eq!(
            forked.fork_point().unwrap().parent_data_root,
            backup.data_root
        );
        // The forked mind carries the parent's state.
        assert_eq!(
            forked.var.get("memory/summary"),
            Some(&b"the docs say: compose, do not reimplement"[..])
        );
        assert_eq!(forked.pedigree.depth(), 1);
    }
}
