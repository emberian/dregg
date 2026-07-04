//! **Agent package** — an agent's config packaged as a signed `.spk`.
//!
//! A hosted agent is configured by four things (docs/THE-GRAIN.md §Commons): its
//! **cap bundle** (the tool facets it may exercise), its **budget** (how much it may
//! spend / how many tool-calls it may make), its **brain choice** (what drives it),
//! and its **roles** (named subsets of the cap bundle a share hands out). This module
//! packages that [`AgentConfig`] as a **real signed Sandstorm `.spk`** and installs it
//! back, verified.
//!
//! ## What we compose (no new crypto)
//!
//! Publishing is exactly [`sandstorm_bridge::SpkBuilder`]: the config's sandstorm-facing
//! view (title + permission facets + roles) becomes the `.spk`'s `sandstorm-manifest`,
//! the full config (with budget + brain) rides as a second archive file, and the whole
//! archive is Ed25519-signed. **The App ID is the signing key** ([`sandstorm_bridge::Spk::app_id`]),
//! so *install-time* provenance is intrinsic and verifiable: "this agent package was
//! authored by key K" is a fact [`install`] proves by checking the signature, not a
//! registry claim.
//!
//! Note the scope of that guarantee. The `.spk`'s App ID is intrinsic because it *is* the
//! verified signature. A **fork pedigree** ([`crate::fork::Pedigree`]) is a *derived*
//! artifact, not a signed one: it is trustworthy only because [`crate::fork::fork_from_package`]
//! binds it to this install-verified App ID and refuses to root a lineage on a backup
//! that does not belong to that app. See `fork.rs` for the exact binding and its residual
//! trust boundary.
//!
//! Installing is [`sandstorm_bridge::Spk::parse`] (which *verifies the signature before
//! it ever hands back an image*) followed by [`sandstorm_bridge::SpkManifest::from_spk`].
//! A package with a single tampered byte fails the signature and yields **no installable
//! config** — the same integrity root a grain launch rests on.

use ed25519_dalek::SigningKey;
use sandstorm_bridge::grain::{GrainSpec, SandboxTier};
use sandstorm_bridge::manifest::AppId;
use sandstorm_bridge::spk::{File, Spk, SpkBuilder, SpkError};
use sandstorm_bridge::SpkManifest;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// The archive path the full [`AgentConfig`] rides at inside the `.spk` (alongside the
/// sandstorm-facing `sandstorm-manifest`). The manifest carries the facets+roles the
/// Sandstorm surface understands; this carries the whole config (budget, brain).
pub const AGENT_CONFIG_PATH: &str = "grain-agent-config.json";

/// What drives a hosted agent. Recorded in the package so a renter knows — and can
/// re-witness — which brain the author shipped (docs/THE-GRAIN.md names the live-LLM
/// brain the honest frontier gap; the package is brain-agnostic).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum BrainChoice {
    /// Deterministic replay of recorded turns (the default, witnessable path).
    Replay,
    /// A scripted body (the confined `deos-hermes` stack's current default).
    Scripted,
    /// A live LLM transport, pinned to a model id (the named frontier gap).
    Llm { model: String },
}

/// The agent's budget: the ceiling its metered spend and tool-calls run against. These
/// are the bounds a light client checks as theorems (`Σδ=0` over the mandate cell,
/// monotone `calls_made`) — here they are the *declared* ceiling the package carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgentBudget {
    /// The maximum value the agent may spend over its lease's life (mandate ceiling).
    pub max_spend: u64,
    /// The maximum number of tool-calls (receipted turns) the agent may make.
    pub max_tool_calls: u64,
}

/// A named subset of the agent's cap facets — a *role* a share hands out (mirrors a
/// Sandstorm sharing role: "editor" = {view, edit}, "viewer" = {view}). A role's
/// facets must be a subset of the agent's cap bundle; [`AgentConfig::validate`] checks it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgentRole {
    pub name: String,
    /// Which of [`AgentConfig::cap_facets`] this role grants.
    pub facets: Vec<String>,
}

/// A hosted agent's configuration — the thing packaged into a signed grain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgentConfig {
    /// The agent's human title (the catalog card's name).
    pub title: String,
    /// **The cap bundle** — the universe of tool facets the agent may exercise. A share
    /// (or a hatched sub-agent) can only attenuate *within* this set.
    pub cap_facets: Vec<String>,
    /// **The roles** — named attenuations of the cap bundle a share confers.
    pub roles: Vec<AgentRole>,
    /// **The budget** — the metered-spend / tool-call ceiling.
    pub budget: AgentBudget,
    /// **The brain** — what drives the agent.
    pub brain: BrainChoice,
}

impl AgentConfig {
    /// A config with a cap bundle, a budget and a brain; no roles.
    pub fn new(
        title: impl Into<String>,
        cap_facets: impl IntoIterator<Item = impl Into<String>>,
        budget: AgentBudget,
        brain: BrainChoice,
    ) -> Self {
        AgentConfig {
            title: title.into(),
            cap_facets: cap_facets.into_iter().map(Into::into).collect(),
            roles: Vec::new(),
            budget,
            brain,
        }
    }

    /// Add a named role (an attenuation of the cap bundle). Builder-style.
    pub fn with_role(
        mut self,
        name: impl Into<String>,
        facets: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        self.roles.push(AgentRole {
            name: name.into(),
            facets: facets.into_iter().map(Into::into).collect(),
        });
        self
    }

    /// Every role must attenuate *within* the cap bundle — a role may not grant a facet
    /// the agent itself does not hold (that would be amplification, not a role). Returns
    /// the offending `(role, facet)` on the first violation.
    pub fn validate(&self) -> Result<(), PackageError> {
        for role in &self.roles {
            for f in &role.facets {
                if !self.cap_facets.contains(f) {
                    return Err(PackageError::RoleExceedsBundle {
                        role: role.name.clone(),
                        facet: f.clone(),
                    });
                }
            }
        }
        Ok(())
    }
}

/// A packaged, installed agent grain: the verified config plus its intrinsic
/// provenance (the App ID = the author's signing key) and the `.spk` content hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainPackage {
    /// **Provenance** — the App ID is the Crockford-base32 of the author's Ed25519
    /// signing key. All packages signed by that key are releases of one author.
    pub app_id: AppId,
    /// The verified agent config (recovered from the signed archive).
    pub config: AgentConfig,
    /// The sha256 of the `.spk` bytes — the content hash a registry listing pins.
    pub spk_hash: [u8; 32],
}

impl GrainPackage {
    /// The sandbox tier a hosted agent grain runs at. An agent runs confined tool-calls
    /// under the same jail a web grain does — never weaker than [`SandboxTier::Caged`].
    pub fn grain_spec(&self) -> GrainSpec {
        GrainSpec {
            app_id: self.app_id.clone(),
            app_version: 1,
            wake_argv: vec!["dregg-agent".into(), "attach".into()],
            ingress_port: None,
            tier: SandboxTier::Caged,
            declared_permissions: self.config.cap_facets.clone(),
        }
    }
}

/// Why packaging / installing an agent grain failed.
#[derive(Debug)]
pub enum PackageError {
    /// A role granted a facet outside the agent's cap bundle (amplification).
    RoleExceedsBundle { role: String, facet: String },
    /// The `.spk` failed to parse or verify — a tampered / mis-signed package yields no
    /// installable config (wraps the `sandstorm-bridge` signature/format error).
    Package(SpkError),
    /// The package's `sandstorm-manifest` could not be decoded.
    Manifest(String),
    /// The package carried no [`AGENT_CONFIG_PATH`] file — not a grain-commons agent
    /// package (a bare Sandstorm app, or a corrupt one).
    NoAgentConfig,
    /// The embedded config could not be deserialized.
    ConfigDecode(String),
    /// The signed manifest's declared facets disagree with the embedded config's cap
    /// bundle — the package is internally inconsistent (refused).
    ConfigManifestMismatch,
}

impl std::fmt::Display for PackageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PackageError::RoleExceedsBundle { role, facet } => write!(
                f,
                "role '{role}' grants facet '{facet}' outside the agent's cap bundle"
            ),
            PackageError::Package(e) => write!(f, "agent package invalid: {e}"),
            PackageError::Manifest(e) => write!(f, "agent manifest decode failed: {e}"),
            PackageError::NoAgentConfig => {
                write!(
                    f,
                    "package carries no {AGENT_CONFIG_PATH} — not an agent grain"
                )
            }
            PackageError::ConfigDecode(e) => write!(f, "agent config decode failed: {e}"),
            PackageError::ConfigManifestMismatch => {
                write!(
                    f,
                    "agent config cap bundle disagrees with the signed manifest"
                )
            }
        }
    }
}
impl std::error::Error for PackageError {}

impl From<SpkError> for PackageError {
    fn from(e: SpkError) -> Self {
        PackageError::Package(e)
    }
}

/// **Publish** an agent config as a signed `.spk`, signed by `signing_key` — the App ID
/// (provenance) is that key. Returns the `.spk` bytes (magic + xz + capnp, Ed25519 over
/// the archive), exactly what [`install`] verifies.
///
/// The config's sandstorm-facing view (title + facets + roles) is written as the
/// `sandstorm-manifest`; the whole config (with budget + brain) rides as [`AGENT_CONFIG_PATH`].
/// Both are inside the signed archive, so both are bound by the signature.
pub fn publish(config: &AgentConfig, signing_key: &SigningKey) -> Result<Vec<u8>, PackageError> {
    config.validate()?;

    // The sandstorm-facing manifest projection (SpkManifest's JSON shape). `app_id` here
    // is ignored on install — from_spk overrides it with the signing key.
    let manifest = serde_json::json!({
        "app_id": "overridden-by-the-signing-key",
        "app_title": config.title,
        "app_version": 1,
        "continue_command": { "argv": ["dregg-agent", "attach"] },
        "bridge_config": {
            "permissions": config.cap_facets,
            "roles": config.roles.iter().map(|r| serde_json::json!({
                "title": r.name,
                "permissions": r.facets,
            })).collect::<Vec<_>>(),
        }
    });
    let manifest_json =
        serde_json::to_string(&manifest).map_err(|e| PackageError::Manifest(e.to_string()))?;
    let config_json =
        serde_json::to_string(config).map_err(|e| PackageError::ConfigDecode(e.to_string()))?;

    let bytes = SpkBuilder::new()
        .manifest_json(&manifest_json)
        .file(File::regular(AGENT_CONFIG_PATH, config_json.into_bytes()))
        .pack(signing_key);
    Ok(bytes)
}

/// **Install** an agent grain from `.spk` bytes: verify the Ed25519 signature (a tampered
/// image is refused *here*, before any config comes back), decode the manifest, recover
/// the embedded config, and cross-check that the signed manifest's declared facets agree
/// with the config's cap bundle. Returns the [`GrainPackage`] — provenance (App ID) +
/// verified config + content hash.
pub fn install(spk_bytes: &[u8]) -> Result<GrainPackage, PackageError> {
    // Signature-verifying parse. A single flipped byte fails here → no installable grain.
    let spk = Spk::parse(spk_bytes)?;
    let manifest =
        SpkManifest::from_spk(&spk).map_err(|e| PackageError::Manifest(e.to_string()))?;

    let cfg_bytes = spk
        .archive
        .find(AGENT_CONFIG_PATH)
        .ok_or(PackageError::NoAgentConfig)?;
    let config: AgentConfig =
        serde_json::from_slice(cfg_bytes).map_err(|e| PackageError::ConfigDecode(e.to_string()))?;

    // Belt-and-suspenders: the signed manifest's facets must match the signed config's
    // cap bundle (both are inside the archive; disagreement means a malformed package).
    let mut declared = manifest.declared_permissions();
    let mut bundle = config.cap_facets.clone();
    declared.sort();
    bundle.sort();
    if declared != bundle {
        return Err(PackageError::ConfigManifestMismatch);
    }
    config.validate()?;

    let mut h = Sha256::new();
    h.update(spk_bytes);
    let spk_hash: [u8; 32] = h.finalize().into();

    Ok(GrainPackage {
        app_id: spk.app_id(),
        config,
        spk_hash,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn sample_config() -> AgentConfig {
        AgentConfig::new(
            "Research Assistant",
            ["web.fetch", "web.search", "notes.write"],
            AgentBudget {
                max_spend: 10_000,
                max_tool_calls: 500,
            },
            BrainChoice::Llm {
                model: "claude-opus-4-8".into(),
            },
        )
        .with_role("reader", ["web.fetch", "web.search"])
        .with_role("author", ["web.fetch", "web.search", "notes.write"])
    }

    #[test]
    fn publish_then_install_roundtrips_the_config() {
        let cfg = sample_config();
        let spk = publish(&cfg, &key(7)).unwrap();
        let pkg = install(&spk).unwrap();
        assert_eq!(pkg.config, cfg);
        // Provenance = the signing key (App ID), not anything the manifest body asserts.
        assert_eq!(pkg.app_id, Spk::parse(&spk).unwrap().app_id());
        // Sandstorm-base32 app id: no padding, none of b/i/l/o.
        assert!(!pkg.app_id.0.contains('='));
    }

    #[test]
    fn a_different_author_key_is_a_different_provenance() {
        let cfg = sample_config();
        let a = install(&publish(&cfg, &key(7)).unwrap()).unwrap();
        let b = install(&publish(&cfg, &key(9)).unwrap()).unwrap();
        // Same config, different signing keys → different App IDs (provenance = key).
        assert_ne!(a.app_id, b.app_id);
    }

    #[test]
    fn a_tampered_package_yields_no_installable_grain() {
        let cfg = sample_config();
        let mut spk = publish(&cfg, &key(7)).unwrap();
        // Flip a byte deep in the signed container.
        let n = spk.len();
        spk[n - 8] ^= 0xff;
        match install(&spk) {
            Err(PackageError::Package(_)) => {}
            other => panic!("tamper not caught: {other:?}"),
        }
    }

    #[test]
    fn a_role_outside_the_bundle_is_refused_at_publish() {
        let cfg = AgentConfig::new(
            "Bad",
            ["view"],
            AgentBudget {
                max_spend: 1,
                max_tool_calls: 1,
            },
            BrainChoice::Replay,
        )
        .with_role("god", ["view", "admin"]); // admin ∉ bundle
        assert!(matches!(
            publish(&cfg, &key(1)),
            Err(PackageError::RoleExceedsBundle { .. })
        ));
    }

    #[test]
    fn the_spk_hash_is_stable_and_content_addressed() {
        let cfg = sample_config();
        let spk = publish(&cfg, &key(7)).unwrap();
        assert_eq!(
            install(&spk).unwrap().spk_hash,
            install(&spk).unwrap().spk_hash
        );
    }
}
