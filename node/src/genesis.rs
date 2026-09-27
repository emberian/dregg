//! Genesis configuration generator for devnet federation setup.
//!
//! Generates:
//! - `genesis.json` — initial federation state
//! - `devnet-node-N.key` — per-node signing keys (hex-encoded, devnet-prefixed)
//! - `node-N.env` — per-node environment variable files
//! - `.devnet` — marker file indicating devnet data directory

use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use dregg_storage_templates::cap_inbox::CAP_INBOX_FACTORY_VK;
use serde::Serialize;
use starbridge_bounty_board::BOUNTY_FACTORY_VK;
use starbridge_compartment_workflow_mandate::CWM_FACTORY_VK;
use starbridge_governed_namespace::GOVERNANCE_FACTORY_VK;
use starbridge_identity::ISSUER_FACTORY_VK;
use starbridge_nameservice::NAME_FACTORY_VK;
use starbridge_privacy_voting::{BALLOT_FACTORY_VK, POLL_FACTORY_VK};
use starbridge_storage_gateway_mandate::SGM_FACTORY_VK;
use starbridge_subscription::SUBSCRIPTION_FACTORY_VK;

/// Deployment coordinate shared by every validator for consensus-time-v1.
pub const CONSENSUS_GENESIS_UNIX_SECONDS_ENV: &str = "DREGG_CONSENSUS_GENESIS_UNIX_SECONDS";
/// Explicit scope label for CTM1: deterministic replay time, not fair wall-clock consensus.
pub const CONSENSUS_TIME_V1_MODE_ENV: &str = "DREGG_CONSENSUS_TIME_V1_MODE";
pub const CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE: &str = "devnet-causal-v1";

/// A validator entry in the genesis configuration.
#[derive(Serialize)]
struct GenesisValidator {
    name: String,
    public_key: String,
    xmss_root: String,
    /// OPTIONAL hex-encoded ML-DSA-65 public key (FIPS 204, 1952 bytes) — the
    /// post-quantum half of the staged `HybridPq` quorum
    /// (`dregg_federation::frost`). ABSENT (the default) means the hybrid is
    /// inactive; the field is skipped when `None` so today's genesis.json is
    /// byte-identical, and every reader parses `validators[]` as loose JSON,
    /// so a future genesis carrying it deserializes everywhere unchanged.
    #[serde(skip_serializing_if = "Option::is_none")]
    ml_dsa_public_key: Option<String>,
    /// OPTIONAL hex-encoded 32-byte HYBRID member id
    /// (`dregg_types::hybrid_id_commitment(ed25519_pk, ml_dsa_pk)`) — the
    /// cryptographic enroll+pin of this member's post-quantum key INTO its
    /// identity. When present, the enrolled ML-DSA roster is DERIVABLE from the
    /// member ids: a verifier recomputes the commitment from a presented
    /// `(ed25519_pk, ml_dsa_pk)` and rejects any ML-DSA key that does not hash
    /// into `hybrid_id` (`dregg_types::verify_committed_ml_dsa`), rather than
    /// trusting a separate out-of-band roster table. Absent (skipped) when the
    /// member has no ML-DSA key, so today's genesis.json is byte-identical.
    #[serde(skip_serializing_if = "Option::is_none")]
    hybrid_id: Option<String>,
}

/// An initial cell in the genesis configuration.
///
/// THE EPOCH §5: `balance` is SIGNED and DECLARATIVE — it is the expected
/// post-seed balance, derived by replaying [`GenesisMove`]s from a
/// value-empty start. The issuer well's declared balance is negative
/// (−total issued supply); every other cell's is non-negative; the column
/// sums to ZERO (`reachable_total_zero`'s genesis hypothesis).
#[derive(Serialize)]
struct GenesisCell {
    id: String,
    public_key: String,
    token_id: String,
    balance: i64,
    /// Hex ML-DSA-65 public key of the cell's owner, when genesis holds the
    /// owner's seed (it derives deterministically from it, exactly as
    /// `AgentCipherclerk` derives the key it signs with).
    ///
    /// LOAD-BEARING, not decoration: `signed_turn_validation::validate_signed_turn`
    /// runs with required-PQ ON at every admission boundary, and it anchors the
    /// ML-DSA key a turn carries in the AGENT CELL's committed `pq_identity`. A
    /// genesis cell materialized without one refuses every hybrid-signed turn it
    /// is the agent of (`pq-identity-not-enrolled`) — so a genesis cell with no
    /// ML-DSA commitment is a cell that cannot act, faucet included.
    #[serde(skip_serializing_if = "Option::is_none")]
    ml_dsa_public_key: Option<String>,
}

/// A genesis ISSUER-MOVE (THE EPOCH §5, "genesis as issuer-moves"): value
/// enters circulation only by moving OUT of the issuer well (which goes
/// negative, carrying −supply). The deployed chain therefore starts inside
/// guarantee B's hypotheses: a value-empty genesis followed by conserving
/// moves.
#[derive(Debug, Clone, Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct GenesisMove {
    /// Hex cell id of the (issuer well) source — debited, may go negative.
    pub from: String,
    /// Hex cell id of the recipient — credited.
    pub to: String,
    /// Amount moved.
    pub amount: u64,
}

/// A starbridge factory cell to materialize on node boot.
#[derive(Debug, Clone, Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct StarbridgeGenesisCell {
    /// Stable devnet label (e.g. `nameservice-registry`).
    pub label: String,
    /// Hex-encoded 32-byte factory VK from the starbridge-app crate.
    pub factory_vk_hex: String,
    /// Demo agent name whose `agent-<name>.key` owns the minted cell.
    pub owner_agent: String,
    /// URI hint used to derive the cell's token domain (e.g. `registry-default`).
    pub uri_hint: String,
}

/// The complete genesis configuration.
#[derive(Serialize)]
struct GenesisConfig {
    /// Hex-encoded 32-byte federation id. COUPLED-CORE: derived from the sorted
    /// committee HYBRID member ids — `hybrid_id_commitment(ed25519, ml_dsa)` per
    /// validator — via [`dregg_federation::derive_federation_id_hybrid_with_epoch`],
    /// so the id commits to the ML-DSA roster, not Ed25519 alone. Closes audit
    /// finding F1: not random bytes anymore.
    federation_id: String,
    /// Application-level deployment domain.  The federation id remains the
    /// canonical commitment to the hybrid committee; this domain scopes the
    /// auxiliary issuer/fee/faucet identities generated below.
    #[serde(skip_serializing_if = "Option::is_none")]
    deployment_domain: Option<String>,
    /// The committee epoch this id was minted for. Always 0 at genesis;
    /// rotated by epoch transitions which mint a fresh id.
    committee_epoch: u64,
    /// One federation-wide time anchor generated once with the deployment bundle.
    ///
    /// Validators load this persisted coordinate; they never derive consensus policy from their
    /// own boot clock. The same value is copied into every `node-N.env` below.
    consensus_genesis_unix_seconds: i64,
    /// Explicitly scopes CTM1 as devnet causal replay time, not federation wall-clock truth.
    consensus_time_mode: &'static str,
    epoch_length: u64,
    checkpoint_interval: u64,
    validators: Vec<GenesisValidator>,
    threshold: usize,
    initial_cells: Vec<GenesisCell>,
    /// THE EPOCH §5: hex cell id of the ISSUER WELL for the default asset.
    /// The runtime registers it with the executor
    /// (`TurnExecutor::register_issuer_well`) so `Burn` executes as a move
    /// target→well.
    issuer_well: String,
    /// THE EPOCH §5: hex cell id of the FEE WELL. The runtime configures it
    /// (`TurnExecutor::set_fee_well_cell`) so fees are moves, not burns.
    fee_well: String,
    /// THE EPOCH §5 ("genesis as issuer-moves"): the seeding moves. The
    /// runtime materializes every `initial_cells` entry at ZERO balance and
    /// then applies these moves; `initial_cells[].balance` is the declared
    /// (checked) outcome.
    genesis_moves: Vec<GenesisMove>,
    /// Hex cell id of the PLAYER GRANT cell — the one deployment-local cell an
    /// application federation issues value INTO at genesis, so a player identity
    /// can pay a turn fee on a chain that has no faucet and no other economy.
    ///
    /// Present exactly when the deployment issues genesis value. Absent means the
    /// column is all zeroes and nothing can act; the PoA deployment gates
    /// (`scripts/poa-devnet-manifest.mjs`, `poa_curator::PoaDeploymentScope`) read
    /// this field to decide WHICH genesis economy the descriptor must be, and the
    /// manifest policy has to agree with it in both directions.
    #[serde(skip_serializing_if = "Option::is_none")]
    player_grant: Option<String>,
    /// Factory cells minted at boot via `starbridge_seed` (devnet only).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    starbridge_cells: Vec<StarbridgeGenesisCell>,
}

/// Optional application-federation policy for [`run_genesis_with_options`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenesisOptions {
    /// Domain mixed into auxiliary genesis-key derivation.  Validator keys stay
    /// random and the federation id remains committee-derived.
    pub deployment_domain: Option<String>,
    /// Seed the generic faucet/demo-agent/Starbridge economy.
    pub seed_demo_economy: bool,
    /// Issue this many units, by ONE issuer-move, into the deployment-local
    /// PLAYER GRANT cell.
    ///
    /// This is the whole economy of an application federation that has no
    /// faucet: `POST /api/faucet` needs a genesis faucet cell an empty-economy
    /// deployment does not have, `Effect::Mint` needs a fee the zero-balance
    /// issuer well cannot pay, and the executor refuses any agent whose balance
    /// is below the turn fee (`turn/src/executor/execute.rs`, `InsufficientBalance`).
    /// With nothing here, a Path of Angels player cannot pay
    /// `dregg_sdk::poa_signal::signal_claim_fee_v1()` and the chain cannot leave
    /// height 0 — which is exactly where it sat until 2026-08-07.
    ///
    /// Requires a `deployment_domain` and no demo economy: the grant identity is
    /// deployment-scoped and the generic devnet economy already funds its own
    /// agents.
    pub player_grant: Option<u64>,
    /// Existing `node-N.key` directory for an explicit successor ceremony.
    /// Every seed is reused or the ceremony refuses; there is no per-validator
    /// fallback to randomness, because that would silently mint a different
    /// federation identity.
    pub validator_key_source: Option<PathBuf>,
}

impl Default for GenesisOptions {
    fn default() -> Self {
        Self {
            deployment_domain: None,
            seed_demo_economy: true,
            player_grant: None,
            validator_key_source: None,
        }
    }
}

/// The key-derivation context the PLAYER GRANT used to be derived from, kept
/// for exactly one purpose: to RECOGNISE and REFUSE that shape.
///
/// ⚑ FLAG DAY 2026-08-07. Until this date the grant seed was
/// `auxiliary_genesis_key(this, deployment_domain, federation_id)`, and BOTH of
/// those inputs are PUBLIC — the domain is a compile-time constant and the
/// federation id is printed in the descriptor every follower pins. The seed was
/// therefore a pure function of published data: whoever could read
/// `genesis.json` could recompute `player-grant.key` and spend the grant. It was
/// bearer value for the whole world, bounded only by the grant amount.
///
/// That derivation is still correct for `issuer-well.key` and `fee-well.key`,
/// and they still use it: a well cannot author a turn (the issuer well's balance
/// is negative and `execute` refuses a negative-balance agent outright), so
/// recomputing a well key buys nothing, while reproducibility of the well cell
/// ids from the descriptor is load-bearing. The grant is different in exactly one
/// way that decides the question: it HOLDS SPENDABLE VALUE. The custody model was
/// carried over from the wells by an instruction that never priced that
/// difference.
///
/// The grant seed is now DRAWN, not derived — see the generator below and
/// [`refuse_derivable_player_grant`], which is what makes the old shape refuse to
/// load rather than be reinterpreted.
pub const REFUSED_DERIVABLE_PLAYER_GRANT_KEY_CONTEXT: &str = "dregg-poa-player-grant-key-v1";

/// Filename of the PLAYER GRANT seed inside a generated deployment bundle.
///
/// ⚑ This file is the SOLE COPY of a spendable identity. It is written 0600 next
/// to `node-N.key` and it is NOT reconstructible from the descriptor: nothing
/// published — not `genesis.json`, not the manifest, not the follower package —
/// determines it. Back it up like a validator seed; losing it strands the grant
/// permanently, and copying it is handing over the grant.
pub const PLAYER_GRANT_KEY_FILE: &str = "player-grant.key";

/// The player-grant cell id a PUBLICLY-DERIVABLE grant WOULD carry, computed
/// from nothing but the descriptor's own public coordinates.
///
/// This is the FORBIDDEN shape, and it exists to be compared against — never to
/// produce a key. `refuse_derivable_player_grant` runs it against a descriptor's
/// declared `player_grant` and refuses on a match.
pub fn derivable_player_grant_cell_id(
    deployment_domain: Option<&str>,
    federation_id: &[u8; 32],
) -> String {
    let secret = auxiliary_genesis_key(
        REFUSED_DERIVABLE_PLAYER_GRANT_KEY_CONTEXT,
        deployment_domain,
        federation_id,
    );
    let public_key = ed25519_dalek::SigningKey::from_bytes(&secret)
        .verifying_key()
        .to_bytes();
    derive_cell_id(&public_key, blake3::hash(b"default").as_bytes())
}

/// THE CUSTODY GATE. Refuse a descriptor whose player-grant cell is the one
/// anyone can recompute from public data.
///
/// FAIL CLOSED, and at LOAD: a pre-flag-day descriptor is not reinterpreted, it
/// is rejected. The generator runs this over the exact bytes it is about to write
/// (so it cannot emit what a node will not load), and `complete_boot_recovery`
/// runs it over the exact bytes a node reads.
///
/// Silent (`Ok`) on any descriptor that issues no grant — the legacy devnet
/// profile and the zero-issuance PoA profile both carry no `player_grant` — and
/// on a grant cell that is not the derivable one, which is every grant this
/// generator now mints.
pub fn refuse_derivable_player_grant(genesis: &serde_json::Value) -> Result<(), String> {
    let Some(declared) = genesis["player_grant"].as_str() else {
        return Ok(());
    };
    let federation_id_hex = genesis["federation_id"]
        .as_str()
        .ok_or_else(|| "descriptor declares a player_grant but no federation_id, so its custody cannot be checked; refusing".to_string())?;
    let federation_id = hex_decode_32(federation_id_hex).ok_or_else(|| {
        format!(
            "descriptor declares a player_grant but its federation_id ({federation_id_hex}) is \
             not 32 hex bytes, so its custody cannot be checked; refusing"
        )
    })?;
    let deployment_domain = genesis["deployment_domain"].as_str();
    let derivable = derivable_player_grant_cell_id(deployment_domain, &federation_id);
    if declared == derivable {
        return Err(format!(
            "REFUSING a descriptor whose player-grant cell {declared} is DERIVABLE from its own \
             public coordinates (deployment_domain {}, federation_id {federation_id_hex}): \
             anyone who can read genesis.json can recompute {PLAYER_GRANT_KEY_FILE} and spend \
             the grant. This is the pre-2026-08-07 shape and it does not load — re-run \
             `dregg-node genesis --player-grant` to draw a fresh grant key and re-genesis.",
            deployment_domain.unwrap_or("<none>")
        ));
    }
    Ok(())
}

/// Run the genesis configuration generation.
pub fn run_genesis(validators: usize, epoch_length: u64, checkpoint_interval: u64, output: &Path) {
    run_genesis_with_options(
        validators,
        epoch_length,
        checkpoint_interval,
        output,
        GenesisOptions::default(),
    );
}

/// Generate genesis through the same committee authority as [`run_genesis`],
/// with an optional application deployment domain and empty-economy profile.
pub fn run_genesis_with_options(
    validators: usize,
    epoch_length: u64,
    checkpoint_interval: u64,
    output: &Path,
    options: GenesisOptions,
) {
    // Genesis MINTS the committee's ML-DSA-65 keys, so it reaches a post-quantum primitive before
    // anything else in this process does. Without this call `dregg_pq`'s fail-closed gate refused
    // the keygen and the command died with `Abort trap: 6` — the documented cold start
    // (`scripts/run-node-10min.sh` step one) could not run at HEAD. The installs lived inline in
    // `run_node` and nowhere else, so serving was covered and cold start was not.
    crate::install_verified_pq_cores();

    if validators == 0 {
        eprintln!("error: must have at least 1 validator");
        std::process::exit(1);
    }

    let deployment_domain = options.deployment_domain.as_deref().map(|domain| {
        if domain.is_empty()
            || domain.len() > 128
            || !domain.bytes().all(|byte| byte.is_ascii_graphic())
        {
            eprintln!(
                "error: --deployment-domain must be 1..128 printable ASCII bytes with no whitespace"
            );
            std::process::exit(1);
        }
        domain
    });
    if deployment_domain.is_some() && options.seed_demo_economy {
        eprintln!(
            "error: --deployment-domain requires --no-demo-economy; the generic faucet endpoint uses the legacy devnet identity"
        );
        std::process::exit(1);
    }

    // ── THE PLAYER GRANT, refused HERE or never. ─────────────────────────────
    // The two poles of the funding decision are decided at the point the operator
    // types the amount, because after this command runs there is a chain, a
    // deployment digest and a signed follower package built on top of the number.
    // A grant that cannot buy one turn is not a small problem to discover later:
    // it produces a deployment that verifies, boots, serves, reports
    // `healthy: true` and refuses every claim.
    let signal_claim_fee = dregg_sdk::poa_signal::signal_claim_fee_v1();
    if let Some(grant) = options.player_grant {
        if deployment_domain.is_none() {
            eprintln!(
                "error: --player-grant requires --deployment-domain; the grant identity is \
                 derived per deployment and an unscoped genesis would mint it into the shared \
                 legacy devnet identity space"
            );
            std::process::exit(1);
        }
        if options.seed_demo_economy {
            eprintln!(
                "error: --player-grant requires --no-demo-economy; the generic devnet economy \
                 already funds its own agents through the faucet"
            );
            std::process::exit(1);
        }
        if grant < signal_claim_fee {
            eprintln!(
                "error: --player-grant {grant} is below the Path of Angels Signal claim fee \
                 {signal_claim_fee}; the grant cell could not pay for a SINGLE turn, so the \
                 deployment would boot healthy and refuse every claim with \
                 `insufficient balance ... need {signal_claim_fee}, have {grant}`. \
                 Fund it for the turns you intend: {signal_claim_fee} buys one."
            );
            std::process::exit(1);
        }
    }

    // Wall time is sampled exactly once while BUILDING the deployment configuration. It is not a
    // validator/replay input: every node receives this same persisted flag-day coordinate.
    let consensus_genesis_unix_seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_else(|e| {
            eprintln!("error: system clock predates Unix epoch: {e}");
            std::process::exit(1);
        })
        .as_secs()
        .try_into()
        .unwrap_or_else(|_| {
            eprintln!("error: system time does not fit consensus-time-v1 i64 coordinate");
            std::process::exit(1);
        });

    // Create output directory.
    std::fs::create_dir_all(output).unwrap_or_else(|e| {
        eprintln!("error: failed to create output directory: {e}");
        std::process::exit(1);
    });

    let validator_key_source = options.validator_key_source.as_deref().map(|source| {
        let source = std::fs::canonicalize(source).unwrap_or_else(|e| {
            eprintln!(
                "error: cannot open --reuse-validator-keys-from {}: {e}",
                source.display()
            );
            std::process::exit(1);
        });
        let output = std::fs::canonicalize(output).unwrap_or_else(|e| {
            eprintln!(
                "error: cannot resolve output directory {}: {e}",
                output.display()
            );
            std::process::exit(1);
        });
        if source == output {
            eprintln!(
                "error: --reuse-validator-keys-from must not be the output directory; a successor \
                 ceremony reads an immutable predecessor bundle and writes a distinct new bundle"
            );
            std::process::exit(1);
        }
        if let Err(error) = validate_validator_seed_set(&source, validators) {
            eprintln!("error: {error}");
            std::process::exit(1);
        }
        source
    });

    // Generate keypairs for each validator. Federation_id is derived from
    // the committee pubkeys AFTER this loop — see below.
    let mut genesis_validators = Vec::with_capacity(validators);
    let mut committee_pubkeys: Vec<dregg_types::PublicKey> = Vec::with_capacity(validators);
    // Aligned index-for-index with `committee_pubkeys`: the published ML-DSA-65
    // key of each validator. Threaded into the COUPLED-CORE federation_id so the
    // committee identity commits to the hybrid roster, not Ed25519 alone.
    let mut committee_ml_dsa: Vec<dregg_federation::frost::MlDsaPublicKey> =
        Vec::with_capacity(validators);

    for i in 0..validators {
        // Draw a new signing key by default. A successor ceremony instead
        // reuses EVERY enrolled validator seed from one explicit predecessor
        // directory. `read_validator_seed` is deliberately fail-closed: one
        // missing or malformed seed must not turn a preserved committee into a
        // partly-random new one while the operator believes identity survived.
        let key_bytes = match validator_key_source.as_deref() {
            Some(source) => read_validator_seed(source, i).unwrap_or_else(|e| {
                eprintln!("error: {e}");
                std::process::exit(1);
            }),
            None => {
                let mut drawn = [0u8; 32];
                getrandom::fill(&mut drawn).expect("getrandom failed");
                drawn
            }
        };

        // Derive the Ed25519 public key.
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
        let public_key = signing_key.verifying_key();
        let pk_hex = hex_encode(public_key.as_bytes());

        // WARNING: This XMSS root is a placeholder for devnet. In production,
        // a real XMSS tree must be generated. See circuit/src/xmss.rs.
        eprintln!(
            "warning: generating placeholder XMSS root for node-{i} (not post-quantum secure)"
        );
        let xmss_root = blake3::derive_key("dregg-devnet-xmss-root-v1", &key_bytes);
        let xmss_root_hex = hex_encode(&xmss_root);

        // HYBRID-PQ: derive this validator's ML-DSA-65 keypair DETERMINISTICALLY
        // from the same 32-byte ed25519 seed (`MlDsaSigningKey::from_seed`), and
        // publish the public key. Deterministic derivation means the running node
        // re-derives its own secret from `node.key` at boot (no separate key file),
        // and every peer reads this published pubkey to verify the PQ half of the
        // member's finalization votes.
        let (ml_dsa_pk, _ml_dsa_sk) =
            dregg_federation::frost::MlDsaSigningKey::from_seed(&key_bytes);
        let ml_dsa_pk_hex = hex_encode(&ml_dsa_pk.0);

        // HYBRID IDENTITY BINDING: the member's canonical id COMMITS to both its
        // ed25519 key and its ML-DSA key, so the enrolled PQ roster is derivable
        // from the id rather than a separate out-of-band table. A verifier
        // recomputes this and rejects any presented ML-DSA key that does not
        // hash into it (`dregg_types::verify_committed_ml_dsa`).
        let hybrid_id = dregg_types::hybrid_id_commitment(&public_key.to_bytes(), &ml_dsa_pk.0);
        let hybrid_id_hex = hex_encode(&hybrid_id);

        committee_pubkeys.push(dregg_types::PublicKey(public_key.to_bytes()));
        committee_ml_dsa.push(ml_dsa_pk.clone());
        genesis_validators.push(GenesisValidator {
            name: format!("node-{i}"),
            public_key: pk_hex,
            xmss_root: xmss_root_hex,
            // HybridPq: the published ML-DSA-65 public key (quantum-safe finality).
            ml_dsa_public_key: Some(ml_dsa_pk_hex),
            // The member id that cryptographically enrolls+pins the ML-DSA key.
            hybrid_id: Some(hybrid_id_hex),
        });

        // Write the key file as raw 32 bytes (matching what the runtime expects).
        let key_path = output.join(format!("node-{i}.key"));
        std::fs::write(&key_path, key_bytes).unwrap_or_else(|e| {
            eprintln!("error: failed to write {}: {e}", key_path.display());
            std::process::exit(1);
        });
        // Issue 6: Restrict key file permissions to owner-only (0o600).
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600))
                .unwrap_or_else(|e| {
                    eprintln!(
                        "error: failed to set permissions on {}: {e}",
                        key_path.display()
                    );
                    std::process::exit(1);
                });
        }

        // Write the env file.
        let env_path = output.join(format!("node-{i}.env"));
        let peers: Vec<String> = (0..validators)
            .filter(|&j| j != i)
            .map(|j| format!("node-{j}:9420"))
            .collect();
        let env_content = node_env_content(i, validators, &peers, consensus_genesis_unix_seconds);
        std::fs::write(&env_path, &env_content).unwrap_or_else(|e| {
            eprintln!("error: failed to write {}: {e}", env_path.display());
            std::process::exit(1);
        });
    }

    // BFT quorum threshold: n - floor((n-1)/3) for n validators.
    let threshold = dregg_federation::quorum_threshold(validators);

    // Derive federation_id = H(sorted committee pubkeys || epoch=0).
    // Closes audit F1: federation_id is now a commitment to the committee,
    // not random bytes. Adding/removing/rekeying a member changes the id.
    let committee_epoch: u64 = 0;
    let federation_id_bytes = dregg_federation::derive_federation_id_hybrid_with_epoch(
        &committee_pubkeys,
        &committee_ml_dsa,
        committee_epoch,
    );
    let federation_id = hex_encode(&federation_id_bytes);

    // Build genesis config.
    //
    // Seed a non-empty ledger so a freshly-deployed devnet boots with real
    // cells (the explorer / `/api/cells` is not empty on first run). Every
    // cell here is a REAL canonical hosted cell: its `id` is the
    // content-addressed `CellId::derive_raw(public_key, token_id)` that the
    // executor will recompute and accept, not a label.
    //
    // THE EPOCH §5 ("genesis as issuer-moves"): value enters by MOVES from
    // the ISSUER WELL, never ex nihilo. The well's declared balance is
    // −total_issued; the faucet/demo balances are the move outcomes; the
    // whole column sums to ZERO, so the deployed chain starts inside
    // guarantee B's hypotheses (`reachable_total_zero`). The FEE WELL starts
    // at zero and accumulates fee moves.
    //
    // THE ASSET: `blake3("default")`, the canonical default token domain (see
    // `executor_setup::default_token_id`). This is NOT cosmetic — a cell's id
    // commits to its asset, and the one application-admission predicate
    // (`signed_turn_validation::validate_signed_turn`, run at HTTP ingress, at
    // finalized-block execution, and in the PG drainer) requires a turn's agent
    // to be `derive_raw(signer, blake3("default"))`. Genesis minted into the
    // all-zero domain until 2026-07-25, which made EVERY genesis cell — the
    // faucet included — unable to act: its owner's signature could not
    // authorize a turn whose agent was that cell. The visible symptom was the
    // faucet answering `success: true` while finalization threw the turn away
    // as `agent-signer-mismatch`, so no recipient was ever credited.
    let default_token_id = *blake3::hash(b"default").as_bytes();

    // The ISSUER WELL cell.  Legacy genesis preserves its deterministic key;
    // an application deployment derives a federation-local key.  Boot reads
    // the explicit `issuer_well` field and registers that exact cell.
    let issuer_well_secret = auxiliary_genesis_key(
        "dregg-devnet-issuer-well-key-v1",
        deployment_domain,
        &federation_id_bytes,
    );
    let issuer_well_signing = ed25519_dalek::SigningKey::from_bytes(&issuer_well_secret);
    let issuer_well_pubkey = issuer_well_signing.verifying_key().to_bytes();
    write_key_file(output, "issuer-well.key", &issuer_well_secret);
    let issuer_well_id = derive_cell_id(&issuer_well_pubkey, &default_token_id);

    // The FEE WELL cell. Deterministic key; starts empty, accumulates fees.
    let fee_well_secret = auxiliary_genesis_key(
        "dregg-devnet-fee-well-key-v1",
        deployment_domain,
        &federation_id_bytes,
    );
    let fee_well_signing = ed25519_dalek::SigningKey::from_bytes(&fee_well_secret);
    let fee_well_pubkey = fee_well_signing.verifying_key().to_bytes();
    write_key_file(output, "fee-well.key", &fee_well_secret);
    let fee_well_id = derive_cell_id(&fee_well_pubkey, &default_token_id);

    // Recipients: faucet supply + demo agents. Every entry becomes one
    // issuer-move well → recipient. Each carries the ML-DSA-65 public key
    // derived from its own seed — the SAME derivation `AgentCipherclerk` uses to
    // sign — so the materialized cell COMMITS the PQ identity its owner will
    // authorize turns with. Without that commitment the hybrid admission
    // predicate refuses every turn the cell is the agent of.
    let mut recipients: Vec<(String, [u8; 32], Vec<u8>, u64)> = Vec::new();
    if options.seed_demo_economy {
        // Legacy/no-domain genesis keeps the exact historical faucet key so
        // POST /api/faucet remains compatible.  A deployment-domain genesis
        // scopes it like every other auxiliary identity.  Application
        // federations use `seed_demo_economy = false` and mint no faucet at all.
        let faucet_secret = auxiliary_genesis_key(
            "dregg-devnet-faucet-key-v1",
            deployment_domain,
            &federation_id_bytes,
        );
        let faucet_signing = ed25519_dalek::SigningKey::from_bytes(&faucet_secret);
        let faucet_pubkey = faucet_signing.verifying_key().to_bytes();
        write_key_file(output, "faucet.key", &faucet_secret);
        recipients.push((
            derive_cell_id(&faucet_pubkey, &default_token_id),
            faucet_pubkey,
            ml_dsa_public_key_for_seed(&faucet_secret),
            1_000_000u64,
        ));
        for (name, amount) in [
            ("alice", 50_000u64),
            ("bob", 25_000u64),
            ("carol", 10_000u64),
        ] {
            let mut key_bytes = [0u8; 32];
            getrandom::fill(&mut key_bytes).expect("getrandom failed");
            let signing = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
            let pubkey = signing.verifying_key().to_bytes();
            write_key_file(output, &format!("agent-{name}.key"), &key_bytes);
            recipients.push((
                derive_cell_id(&pubkey, &default_token_id),
                pubkey,
                ml_dsa_public_key_for_seed(&key_bytes),
                amount,
            ));
        }
    }

    // The PLAYER GRANT cell — the whole economy of an application federation.
    // It is an ordinary recipient of an ordinary issuer-move: no minting, no
    // special case in the loader, and the column still sums to zero. What makes
    // it usable rather than decorative is the ML-DSA commitment below: hybrid
    // admission anchors the PQ key a turn carries in the AGENT CELL's committed
    // `pq_identity`, so a grant cell without one is a funded cell that refuses
    // every turn it is the agent of (`pq-identity-not-enrolled`).
    //
    // ⚑ CUSTODY: THE GRANT SEED IS DRAWN, NOT DERIVED. This is the one auxiliary
    // identity that holds spendable value, so it is generated exactly like a
    // validator seed — 32 bytes from the OS CSPRNG, written 0600, and NOT a
    // function of anything the descriptor publishes. The wells above keep their
    // deterministic derivation because a well cannot author a turn and because
    // reproducing their cell ids from the descriptor is load-bearing; the grant
    // had that same derivation until 2026-08-07, which made it bearer value for
    // anyone who could read `genesis.json`. See
    // `REFUSED_DERIVABLE_PLAYER_GRANT_KEY_CONTEXT`.
    //
    // The descriptor carries only what a verifier needs and nothing the secret
    // follows from: the cell id, the ed25519 public key, and the ML-DSA public
    // key. The seed leaves this function only into `PLAYER_GRANT_KEY_FILE`.
    let player_grant_id = options.player_grant.map(|amount| {
        let mut secret = [0u8; 32];
        getrandom::fill(&mut secret).expect("getrandom failed");
        let pubkey = ed25519_dalek::SigningKey::from_bytes(&secret)
            .verifying_key()
            .to_bytes();
        write_key_file(output, PLAYER_GRANT_KEY_FILE, &secret);
        let id = derive_cell_id(&pubkey, &default_token_id);
        recipients.push((
            id.clone(),
            pubkey,
            ml_dsa_public_key_for_seed(&secret),
            amount,
        ));
        id
    });

    let total_issued: u64 = recipients.iter().map(|(_, _, _, amt)| amt).sum();
    let genesis_moves: Vec<GenesisMove> = recipients
        .iter()
        .map(|(id, _, _, amount)| GenesisMove {
            from: issuer_well_id.clone(),
            to: id.clone(),
            amount: *amount,
        })
        .collect();

    // Declared post-seed balances: the well carries −supply; the column
    // sums to zero.
    let mut initial_cells = vec![
        GenesisCell {
            id: issuer_well_id.clone(),
            public_key: hex_encode(&issuer_well_pubkey),
            token_id: hex_encode(&default_token_id),
            balance: -(total_issued as i64),
            ml_dsa_public_key: Some(hex_encode(&ml_dsa_public_key_for_seed(&issuer_well_secret))),
        },
        GenesisCell {
            id: fee_well_id.clone(),
            public_key: hex_encode(&fee_well_pubkey),
            token_id: hex_encode(&default_token_id),
            balance: 0,
            ml_dsa_public_key: Some(hex_encode(&ml_dsa_public_key_for_seed(&fee_well_secret))),
        },
    ];
    for (id, pubkey, ml_dsa_pubkey, amount) in &recipients {
        initial_cells.push(GenesisCell {
            id: id.clone(),
            public_key: hex_encode(pubkey),
            token_id: hex_encode(&default_token_id),
            balance: *amount as i64,
            ml_dsa_public_key: Some(hex_encode(ml_dsa_pubkey)),
        });
    }
    // CONSERVATION, checked in every profile.
    //
    // ⚑ This was a `debug_assert_eq!`, which is compiled OUT of a release build —
    // so the one property that makes an issuer-move genesis different from minting
    // from nowhere was checked exactly where nobody generates a deployment, and not
    // checked in the binary an operator actually runs. A genesis is written ONCE
    // and then hashed into a deployment id, a manifest, a follower package and a
    // signed authority head; if the column does not close, all of that pins a chain
    // whose supply is a lie. Refuse instead.
    let column: i128 = initial_cells
        .iter()
        .map(|c| c.balance as i128)
        .sum::<i128>();
    if column != 0 {
        eprintln!(
            "error: genesis value column sums to {column}, not zero; value would enter this \
             chain from nowhere. Refusing to write a descriptor that does not conserve."
        );
        std::process::exit(1);
    }

    let starbridge_cells = if options.seed_demo_economy {
        default_starbridge_genesis_cells()
    } else {
        Vec::new()
    };

    let genesis = GenesisConfig {
        federation_id,
        deployment_domain: deployment_domain.map(str::to_owned),
        committee_epoch,
        consensus_genesis_unix_seconds,
        consensus_time_mode: CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE,
        epoch_length,
        checkpoint_interval,
        validators: genesis_validators,
        threshold,
        initial_cells,
        issuer_well: issuer_well_id,
        // Upstream's standalone fee-well cell stands in FRESH genesis; the
        // fork's revolving fund (fee well == faucet) applies on the
        // genesis-less devnet via the lib.rs backfill, which is the mode the
        // cave node actually runs.
        fee_well: fee_well_id,
        genesis_moves,
        player_grant: player_grant_id,
        starbridge_cells,
    };

    // Write genesis.json.
    let genesis_path = output.join("genesis.json");
    let genesis_json = serde_json::to_string_pretty(&genesis).expect("failed to serialize genesis");

    // THE CUSTODY GATE, over the EXACT BYTES about to be written — the same
    // function `complete_boot_recovery` runs over the exact bytes a node reads.
    // The generator refuses to emit a descriptor no node would load, so a revert
    // of the grant derivation dies here, at the first `dregg-node genesis`, and
    // not on a deployed chain holding bearer value.
    {
        let as_loaded: serde_json::Value =
            serde_json::from_str(&genesis_json).expect("the descriptor we just serialized parses");
        if let Err(reason) = refuse_derivable_player_grant(&as_loaded) {
            eprintln!("error: {reason}");
            std::process::exit(1);
        }
    }

    std::fs::write(&genesis_path, &genesis_json).unwrap_or_else(|e| {
        eprintln!("error: failed to write genesis.json: {e}");
        std::process::exit(1);
    });

    // Write `.devnet` marker so the runtime can detect devnet data directories.
    let devnet_marker_path = output.join(".devnet");
    std::fs::write(
        &devnet_marker_path,
        "# This directory contains devnet configuration.\n# Keys here are NOT production-grade.\n",
    )
    .unwrap_or_else(|e| {
        eprintln!("error: failed to write .devnet marker: {e}");
        std::process::exit(1);
    });

    println!(
        "Devnet genesis configuration generated in {}",
        output.display()
    );
    println!("  Federation ID: {}", genesis.federation_id);
    println!("  Validators: {validators}");
    println!("  Threshold: {threshold}");
    println!("  Epoch length: {epoch_length}");
    println!("  Checkpoint interval: {checkpoint_interval}");
    if let Some(domain) = &genesis.deployment_domain {
        println!("  Deployment domain: {domain}");
    }
    println!("  Demo economy: {}", options.seed_demo_economy);
    if let Some(source) = validator_key_source {
        println!(
            "  Committee: REUSED from {} (explicit successor ceremony)",
            source.display()
        );
    } else {
        println!("  Committee: newly drawn");
    }
    match (&genesis.player_grant, options.player_grant) {
        (Some(id), Some(amount)) => {
            println!("  Player grant: {amount} into cell {id}");
            println!(
                "    one Signal claim costs {signal_claim_fee}, so this buys {} turn(s)",
                amount / signal_claim_fee
            );
            println!(
                "    ⚑ {} is the SOLE COPY of the key that spends this grant. It was DRAWN \
                 from the OS CSPRNG, written 0600, and NOTHING published — not this descriptor, \
                 not the manifest, not the follower package — determines it. Back it up like a \
                 validator seed; copying it is handing over the grant, and losing it strands \
                 the grant permanently (there is no re-derivation).",
                output.join(PLAYER_GRANT_KEY_FILE).display()
            );
        }
        _ => println!(
            "  Player grant: NONE — the value column is all zeroes, so no cell can pay a turn \
             fee and this chain cannot leave height 0. Pass --player-grant to fund one."
        ),
    }
    println!();
    println!("Files:");
    println!("  {}", genesis_path.display());
    println!("  {}", devnet_marker_path.display());
    for i in 0..validators {
        println!("  {}", output.join(format!("node-{i}.key")).display());
        println!("  {}", output.join(format!("node-{i}.env")).display());
    }
    println!();
    println!("WARNING: These keys are for devnet use only. Do NOT use in production.");
}

/// Default starbridge factory cells for devnet composition.
///
/// VK bytes are taken from each starbridge-app crate's public constant so
/// genesis.json stays aligned with the deployed factory descriptors.
pub fn default_starbridge_genesis_cells() -> Vec<StarbridgeGenesisCell> {
    vec![
        StarbridgeGenesisCell {
            label: "nameservice-registry".into(),
            factory_vk_hex: hex_encode(&NAME_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "registry-default".into(),
        },
        StarbridgeGenesisCell {
            label: "identity-issuer".into(),
            factory_vk_hex: hex_encode(&ISSUER_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "issuer-default".into(),
        },
        StarbridgeGenesisCell {
            label: "subscription-topic".into(),
            factory_vk_hex: hex_encode(&SUBSCRIPTION_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "topic-default".into(),
        },
        StarbridgeGenesisCell {
            label: "governed-namespace-root".into(),
            factory_vk_hex: hex_encode(&GOVERNANCE_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "namespace-default".into(),
        },
        StarbridgeGenesisCell {
            label: "cwm-mandate".into(),
            factory_vk_hex: hex_encode(&CWM_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "mandate-default".into(),
        },
        StarbridgeGenesisCell {
            label: "sgm-gateway".into(),
            factory_vk_hex: hex_encode(&SGM_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "gateway-default".into(),
        },
        StarbridgeGenesisCell {
            label: "privacy-voting-poll".into(),
            factory_vk_hex: hex_encode(&POLL_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "poll-default".into(),
        },
        StarbridgeGenesisCell {
            label: "privacy-voting-ballot".into(),
            factory_vk_hex: hex_encode(&BALLOT_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "ballot-default".into(),
        },
        StarbridgeGenesisCell {
            label: "bounty-board-bounty".into(),
            factory_vk_hex: hex_encode(&BOUNTY_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "bounty-default".into(),
        },
        // The storage-template CapInbox factory (mailbox organ). Seeded
        // exactly like the subscription factory above: the descriptor is
        // registered by `starbridge_seed::register_starbridge_factory_descriptors`
        // and this entry births the default inbox cell at boot.
        StarbridgeGenesisCell {
            label: "cap-inbox".into(),
            factory_vk_hex: hex_encode(&CAP_INBOX_FACTORY_VK),
            owner_agent: "alice".into(),
            uri_hint: "inbox-default".into(),
        },
    ]
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Decode exactly 32 hex bytes, or nothing. Used by the custody gate, which must
/// be able to read a descriptor's federation id without depending on the node's
/// boot-time decoders (it runs inside `dregg-node genesis`, before a node exists).
fn hex_decode_32(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(hex.get(index * 2..index * 2 + 2)?, 16).ok()?;
    }
    Some(out)
}

fn node_env_content(
    node_index: usize,
    federation_size: usize,
    peers: &[String],
    consensus_genesis_unix_seconds: i64,
) -> String {
    format!(
        "RUST_LOG=info\n\
         DREGG_NODE_INDEX={node_index}\n\
         DREGG_FEDERATION_SIZE={federation_size}\n\
         DREGG_FEDERATION_PEERS={peers}\n\
         DREGG_DATA_DIR=/data\n\
         DREGG_PORT=8420\n\
         DREGG_GOSSIP_PORT=9420\n\
         {consensus_time_env}={consensus_genesis_unix_seconds}\n\
         {consensus_mode_env}={consensus_mode}\n",
        peers = peers.join(","),
        consensus_time_env = CONSENSUS_GENESIS_UNIX_SECONDS_ENV,
        consensus_mode_env = CONSENSUS_TIME_V1_MODE_ENV,
        consensus_mode = CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE,
    )
}

/// The deterministic devnet ISSUER WELL cell id — the same derivation
/// [`run_genesis`] uses (key context `dregg-devnet-issuer-well-key-v1`, the
/// canonical default asset). Lets the runtime (faucet backfill,
/// `starbridge_seed`) locate the well without re-reading genesis.json.
pub fn devnet_issuer_well_id() -> dregg_cell::CellId {
    let secret = blake3::derive_key("dregg-devnet-issuer-well-key-v1", b"genesis");
    let pubkey = ed25519_dalek::SigningKey::from_bytes(&secret)
        .verifying_key()
        .to_bytes();
    dregg_cell::Cell::with_balance(pubkey, crate::executor_setup::default_token_id(), 0).id()
}

/// The deterministic devnet FAUCET cell id — the cell [`run_genesis`] mints the
/// faucet supply into, and the cell `POST /api/faucet` spends from. Both sides
/// derive it from the same key context in the same asset; `api.rs` pins them
/// together in `genesis_faucet_cell_matches_the_endpoint_faucet_cell`.
pub fn devnet_faucet_cell_id() -> dregg_cell::CellId {
    let secret = blake3::derive_key("dregg-devnet-faucet-key-v1", b"genesis");
    let pubkey = ed25519_dalek::SigningKey::from_bytes(&secret)
        .verifying_key()
        .to_bytes();
    dregg_cell::Cell::with_balance(pubkey, crate::executor_setup::default_token_id(), 0).id()
}

/// The ML-DSA-65 public key an `AgentCipherclerk` built from `seed` signs with
/// (`MlDsaTurnKey::from_ed25519_seed`, the same derivation
/// `AgentCipherclerk::ml_dsa_key` uses). Genesis publishes it so the
/// materialized cell commits the identity that will authorize its turns.
fn ml_dsa_public_key_for_seed(seed: &[u8; 32]) -> Vec<u8> {
    dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(seed).public_bytes()
}

/// Derive an auxiliary genesis identity.  No deployment domain preserves the
/// legacy devnet bytes exactly.  A named application federation includes both
/// its public domain and its committee-derived federation id, so neither a
/// same-domain fresh genesis nor a different domain can reuse the identity.
fn auxiliary_genesis_key(
    context: &str,
    deployment_domain: Option<&str>,
    federation_id: &[u8; 32],
) -> [u8; 32] {
    let Some(domain) = deployment_domain else {
        return blake3::derive_key(context, b"genesis");
    };
    let mut material = Vec::with_capacity(domain.len() + 1 + federation_id.len());
    material.extend_from_slice(domain.as_bytes());
    material.push(0);
    material.extend_from_slice(federation_id);
    blake3::derive_key(context, &material)
}

/// Derive the canonical content-addressed `CellId` for a hosted cell, using the
/// exact same path the runtime (`materialize_genesis_cells`) recomputes:
/// `dregg_cell::Cell::with_balance(pk, token, _).id()`. This guarantees the
/// `id` written into genesis.json matches the executor's derivation, so the
/// cell materializes instead of being rejected as a mismatched id.
fn derive_cell_id(public_key: &[u8; 32], token_id: &[u8; 32]) -> String {
    let cell = dregg_cell::Cell::with_balance(*public_key, *token_id, 0);
    hex_encode(&cell.id().0)
}

/// Write a raw 32-byte key file with owner-only (0o600) permissions.
fn write_key_file(output: &Path, name: &str, key_bytes: &[u8; 32]) {
    let key_path = output.join(name);
    std::fs::write(&key_path, key_bytes).unwrap_or_else(|e| {
        eprintln!("error: failed to write {}: {e}", key_path.display());
        std::process::exit(1);
    });
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600)).unwrap_or_else(
            |e| {
                eprintln!(
                    "error: failed to set permissions on {}: {e}",
                    key_path.display()
                );
                std::process::exit(1);
            },
        );
    }
}

/// Read one predecessor validator seed for an explicit successor ceremony.
///
/// This is kept as a Result boundary so the dangerous inputs are unit-testable
/// without spawning a process merely to observe its exit code. The ceremony
/// converts any error into a whole-command refusal; it never falls back to a
/// fresh key after the operator asked to preserve committee identity.
fn read_validator_seed(source: &Path, index: usize) -> Result<[u8; 32], String> {
    let path = source.join(format!("node-{index}.key"));
    let metadata = std::fs::symlink_metadata(&path).map_err(|e| {
        format!(
            "successor ceremony cannot read required predecessor seed {}: {e}; refusing instead \
             of silently drawing a different validator",
            path.display()
        )
    })?;
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return Err(format!(
            "successor ceremony requires {} to be a regular file, not a link or special file",
            path.display()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = metadata.permissions().mode() & 0o777;
        if mode & 0o077 != 0 {
            return Err(format!(
                "successor ceremony requires {} to be owner-only (0600 or stricter), found {:03o}",
                path.display(),
                mode
            ));
        }
    }
    let bytes = std::fs::read(&path)
        .map_err(|e| format!("cannot read predecessor seed {}: {e}", path.display()))?;
    bytes.try_into().map_err(|bytes: Vec<u8>| {
        format!(
            "successor ceremony requires {} to contain exactly 32 raw bytes, found {}",
            path.display(),
            bytes.len()
        )
    })
}

/// Refuse a subset/superset ceremony. Reusing one key from a larger predecessor
/// committee does not preserve its federation identity, even though every key
/// this invocation asks for exists; the named `node-N.key` set must therefore
/// equal the requested committee exactly.
fn validate_validator_seed_set(source: &Path, validators: usize) -> Result<(), String> {
    let expected: std::collections::BTreeSet<String> = (0..validators)
        .map(|index| format!("node-{index}.key"))
        .collect();
    let mut found = std::collections::BTreeSet::new();
    let entries = std::fs::read_dir(source).map_err(|e| {
        format!(
            "cannot enumerate predecessor validator directory {}: {e}",
            source.display()
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|e| {
            format!(
                "cannot enumerate predecessor validator directory {}: {e}",
                source.display()
            )
        })?;
        let Some(name) = entry.file_name().to_str().map(str::to_owned) else {
            continue;
        };
        if name.starts_with("node-") && name.ends_with(".key") {
            found.insert(name);
        }
    }
    if found != expected {
        return Err(format!(
            "successor ceremony requires the predecessor validator seed set to equal the requested \
             committee exactly; expected {:?}, found {:?}. Refusing a subset/superset ceremony that \
             would silently change federation identity",
            expected, found
        ));
    }
    Ok(())
}

#[cfg(test)]
mod custody {
    //! ⚑ THE PLAYER-GRANT CUSTODY FALSIFIER.
    //!
    //! One property, stated so it can go red: **the descriptor and every other
    //! published artifact do not determine the grant secret.** Until 2026-08-07
    //! they did — the seed was `auxiliary_genesis_key(context, deployment_domain,
    //! federation_id)` over two public inputs — so a funded cell was bearer value
    //! for anyone who could read `genesis.json`.
    //!
    //! The two poles, both held here:
    //!
    //! * the WELLS still reproduce EXACTLY from public data (their derivation is
    //!   sound — a well cannot author a turn — and reproducibility is
    //!   load-bearing), checked by re-deriving them from each descriptor's own
    //!   `(deployment_domain, federation_id)` and demanding a byte match;
    //! * the GRANT does not, checked by running the SAME derivation over the SAME
    //!   public inputs and demanding a MISS.
    //!
    //! The miss is what goes red on a revert: re-derive the grant from public
    //! inputs and `grade_grant_custody` fails on the very next run. That is not
    //! an argument — `a_re_derived_bundle_is_graded_red` CONSTRUCTS the
    //! pre-flag-day bundle out of the derivation the wells still use, asserts the
    //! mutation actually changed the bytes on disk, and feeds it to the same
    //! grader the real ceremony passes.

    use super::*;
    use std::path::Path;

    const DOMAIN: &str = "pathofangels.network/federation/v1";
    const GRANT: u64 = 100_000;

    /// Generate one real deployment bundle, exactly as `scripts/poa-devnet.sh
    /// genesis` does: deployment-scoped, no demo economy, one funded grant.
    fn ceremony(output: &Path) {
        run_genesis_with_options(
            1,
            1000,
            100,
            output,
            GenesisOptions {
                deployment_domain: Some(DOMAIN.to_owned()),
                seed_demo_economy: false,
                player_grant: Some(GRANT),
                validator_key_source: None,
            },
        );
    }

    fn descriptor(bundle: &Path) -> serde_json::Value {
        serde_json::from_slice(&std::fs::read(bundle.join("genesis.json")).expect("descriptor"))
            .expect("descriptor JSON")
    }

    fn seed(bundle: &Path, name: &str) -> [u8; 32] {
        std::fs::read(bundle.join(name))
            .unwrap_or_else(|e| panic!("{name} must be in the bundle: {e}"))
            .try_into()
            .expect("a 32-byte Ed25519 seed")
    }

    /// GRADE one generated bundle against the custody property, using ONLY what
    /// the descriptor publishes. `Err` names the failure the way an auditor would.
    ///
    /// This is the single grader both poles run through: the real ceremony must
    /// pass it, and a bundle whose grant was re-derived from public inputs must
    /// not.
    fn grade_grant_custody(bundle: &Path) -> Result<(), String> {
        let genesis = descriptor(bundle);
        let federation_id =
            hex_decode_32(genesis["federation_id"].as_str().expect("federation_id"))
                .expect("32-byte federation id");
        let domain = genesis["deployment_domain"].as_str();

        // POLE 1 — THE WELLS REPRODUCE. Their derivation is unchanged and it is
        // load-bearing: a verifier holding nothing but the descriptor recomputes
        // both well identities and both well cell ids, to the byte.
        for (context, file, field) in [
            (
                "dregg-devnet-issuer-well-key-v1",
                "issuer-well.key",
                "issuer_well",
            ),
            ("dregg-devnet-fee-well-key-v1", "fee-well.key", "fee_well"),
        ] {
            let derived = auxiliary_genesis_key(context, domain, &federation_id);
            if derived != seed(bundle, file) {
                return Err(format!(
                    "{file} is NOT reproducible from the descriptor's public coordinates — the \
                     wells' derivation is load-bearing and must not have changed"
                ));
            }
            let derived_id = derive_cell_id(
                &ed25519_dalek::SigningKey::from_bytes(&derived)
                    .verifying_key()
                    .to_bytes(),
                blake3::hash(b"default").as_bytes(),
            );
            if genesis[field].as_str() != Some(derived_id.as_str()) {
                return Err(format!(
                    "the descriptor's {field} is not the cell the public derivation produces"
                ));
            }
        }

        // POLE 2 — THE GRANT DOES NOT. Same derivation, same public inputs, and
        // it must MISS: both the seed on disk and the cell id in the descriptor.
        let would_be = auxiliary_genesis_key(
            REFUSED_DERIVABLE_PLAYER_GRANT_KEY_CONTEXT,
            domain,
            &federation_id,
        );
        if would_be == seed(bundle, PLAYER_GRANT_KEY_FILE) {
            return Err(format!(
                "{PLAYER_GRANT_KEY_FILE} IS the key `auxiliary_genesis_key` derives from the \
                 PUBLIC (deployment_domain, federation_id) — anyone who can read genesis.json \
                 can spend this grant"
            ));
        }
        if genesis["player_grant"].as_str()
            == Some(derivable_player_grant_cell_id(domain, &federation_id).as_str())
        {
            return Err(
                "the descriptor's player_grant cell is the publicly-derivable one".to_string(),
            );
        }

        // And the shipped gate agrees with this hand grading.
        refuse_derivable_player_grant(&genesis)
    }

    /// THE PROPERTY: a successor ceremony can preserve the exact committee while
    /// still drawing a fresh, non-derivable player grant. This is the live PoA
    /// re-genesis case: federation identity remains pinned, while the deployment
    /// descriptor and custody-bearing player identity are honestly new.
    #[test]
    fn successor_reuses_the_committee_and_never_the_player_grant() {
        let first = tempfile::tempdir().expect("tempdir");
        let second = tempfile::tempdir().expect("tempdir");
        ceremony(first.path());
        run_genesis_with_options(
            1,
            1000,
            100,
            second.path(),
            GenesisOptions {
                deployment_domain: Some(DOMAIN.to_owned()),
                seed_demo_economy: false,
                player_grant: Some(GRANT),
                validator_key_source: Some(first.path().to_owned()),
            },
        );

        grade_grant_custody(first.path()).expect("ceremony 1 custody");
        grade_grant_custody(second.path()).expect("ceremony 2 custody");

        assert_eq!(
            seed(first.path(), "node-0.key"),
            seed(second.path(), "node-0.key"),
            "the explicit successor operation must preserve the validator seed"
        );
        assert_eq!(
            descriptor(first.path())["federation_id"],
            descriptor(second.path())["federation_id"],
            "the same hybrid committee and epoch must preserve federation identity"
        );
        assert_eq!(
            descriptor(first.path())["validators"],
            descriptor(second.path())["validators"],
            "the whole enrolled hybrid roster must be byte-identical"
        );

        // Same domain, committee, generator, and amount — and two different
        // grant secrets/cells. The successor flag preserves ONLY validator
        // custody; it must never duplicate the spendable player identity.
        assert_ne!(
            seed(first.path(), PLAYER_GRANT_KEY_FILE),
            seed(second.path(), PLAYER_GRANT_KEY_FILE),
            "two ceremonies must not share a grant key"
        );
        assert_ne!(
            descriptor(first.path())["player_grant"],
            descriptor(second.path())["player_grant"],
            "two ceremonies must not share a grant cell"
        );
        assert_ne!(
            std::fs::read(first.path().join("genesis.json")).expect("first genesis"),
            std::fs::read(second.path().join("genesis.json")).expect("second genesis"),
            "a successor descriptor must remain distinct even when the committee is preserved"
        );

        // The grant amount, the fee well and the conservation column are NOT what
        // this change touched, and the bundle still says so.
        let genesis = descriptor(first.path());
        let column: i64 = genesis["initial_cells"]
            .as_array()
            .expect("initial_cells")
            .iter()
            .map(|cell| cell["balance"].as_i64().expect("signed balance"))
            .sum();
        assert_eq!(column, 0, "the value column still sums to zero");
        assert_eq!(
            genesis["genesis_moves"].as_array().map(Vec::len),
            Some(1),
            "still exactly one issuer-move"
        );
    }

    #[test]
    fn successor_seed_reader_refuses_missing_malformed_linked_and_loose_keys() {
        use std::fs;

        let source = tempfile::tempdir().expect("tempdir");
        let key = source.path().join("node-0.key");

        assert!(
            read_validator_seed(source.path(), 0)
                .expect_err("missing key must refuse")
                .contains("silently drawing")
        );

        fs::write(&key, [0x31; 31]).expect("short key");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&key, fs::Permissions::from_mode(0o600)).expect("owner mode");
        }
        assert!(
            read_validator_seed(source.path(), 0)
                .expect_err("short key must refuse")
                .contains("exactly 32")
        );

        fs::write(&key, [0x32; 32]).expect("valid key");
        #[cfg(unix)]
        {
            use std::os::unix::fs::{PermissionsExt, symlink};

            fs::set_permissions(&key, fs::Permissions::from_mode(0o644)).expect("loose mode");
            assert!(
                read_validator_seed(source.path(), 0)
                    .expect_err("loose key must refuse")
                    .contains("owner-only")
            );
            fs::set_permissions(&key, fs::Permissions::from_mode(0o600)).expect("owner mode");
            assert_eq!(read_validator_seed(source.path(), 0), Ok([0x32; 32]));

            fs::write(source.path().join("node-1.key"), [0x33; 32]).expect("extra key");
            assert!(
                validate_validator_seed_set(source.path(), 1)
                    .expect_err("a committee subset must refuse")
                    .contains("subset/superset")
            );
            fs::remove_file(source.path().join("node-1.key")).expect("remove extra key");
            assert_eq!(validate_validator_seed_set(source.path(), 1), Ok(()));

            let linked_source = tempfile::tempdir().expect("linked tempdir");
            symlink(&key, linked_source.path().join("node-0.key")).expect("symlink");
            assert!(
                read_validator_seed(linked_source.path(), 0)
                    .expect_err("linked key must refuse")
                    .contains("regular file")
            );
        }
    }

    /// THE FALSIFIER, RUN. Rebuild the pre-2026-08-07 bundle — grant seed and
    /// grant cell derived from the public `(domain, federation_id)`, which is
    /// literally the code this commit removed — and watch the grader reject it.
    ///
    /// The mutation is CONSTRUCTED from `auxiliary_genesis_key`, the function the
    /// wells still call, so it cannot rot into a no-op the way a string-replace
    /// mutation does; and the assertion below proves the bytes on disk actually
    /// changed before any verdict is read.
    #[test]
    fn a_re_derived_bundle_is_graded_red() {
        let bundle = tempfile::tempdir().expect("tempdir");
        ceremony(bundle.path());
        grade_grant_custody(bundle.path()).expect("the freshly drawn bundle is green");

        let mut genesis = descriptor(bundle.path());
        let federation_id =
            hex_decode_32(genesis["federation_id"].as_str().expect("federation_id"))
                .expect("32-byte federation id");

        // ── the pre-flag-day generator, reconstructed ────────────────────────
        let re_derived = auxiliary_genesis_key(
            REFUSED_DERIVABLE_PLAYER_GRANT_KEY_CONTEXT,
            Some(DOMAIN),
            &federation_id,
        );
        let drawn = seed(bundle.path(), PLAYER_GRANT_KEY_FILE);
        assert_ne!(
            drawn, re_derived,
            "THE MUTATION MUST BE A MUTATION: if these already agree the generator is \
             already deriving the grant and this test is grading nothing"
        );
        std::fs::write(bundle.path().join(PLAYER_GRANT_KEY_FILE), re_derived)
            .expect("overwrite the grant seed with the derivable one");
        genesis["player_grant"] =
            serde_json::Value::String(derivable_player_grant_cell_id(Some(DOMAIN), &federation_id));
        std::fs::write(
            bundle.path().join("genesis.json"),
            serde_json::to_vec_pretty(&genesis).expect("serialize"),
        )
        .expect("overwrite the descriptor");
        assert_eq!(
            seed(bundle.path(), PLAYER_GRANT_KEY_FILE),
            re_derived,
            "the mutation reached the disk"
        );

        // ── and the verdict ──────────────────────────────────────────────────
        let refusal = grade_grant_custody(bundle.path())
            .expect_err("a grant re-derived from public inputs MUST be graded red");
        eprintln!("\n  RED (custody grader): {refusal}");
        assert!(
            refusal.contains(PLAYER_GRANT_KEY_FILE) || refusal.contains("player_grant"),
            "the refusal must name what is derivable: {refusal}"
        );

        // The SHIPPED gate — the one `dregg-node genesis` runs before writing and
        // `complete_boot_recovery` runs before serving — refuses the same bundle.
        let boot = refuse_derivable_player_grant(&descriptor(bundle.path()))
            .expect_err("the boot gate must refuse a derivable grant");
        eprintln!("  RED (shipped gate):    {boot}\n");
        assert!(
            boot.contains("DERIVABLE") && boot.contains("re-genesis"),
            "the boot refusal must say what is wrong and what to do: {boot}"
        );
    }

    /// The gate is silent where it must be, and loud where it must be — including
    /// the worst case, a grant minted with NO deployment domain, whose derivable
    /// key is a global constant shared by every unscoped deployment.
    #[test]
    fn the_custody_gate_refuses_only_the_derivable_shape() {
        let federation_id = [0x5c; 32];
        let federation_hex = hex_encode(&federation_id);

        // No grant at all — the legacy devnet and zero-issuance PoA profiles.
        assert!(
            refuse_derivable_player_grant(&serde_json::json!({
                "federation_id": federation_hex,
                "deployment_domain": DOMAIN,
            }))
            .is_ok(),
            "a descriptor that issues no grant has no grant custody to refuse"
        );

        // A drawn grant — the shape this generator now mints.
        let drawn = derive_cell_id(
            &ed25519_dalek::SigningKey::from_bytes(&[0x9e; 32])
                .verifying_key()
                .to_bytes(),
            blake3::hash(b"default").as_bytes(),
        );
        assert!(
            refuse_derivable_player_grant(&serde_json::json!({
                "federation_id": federation_hex,
                "deployment_domain": DOMAIN,
                "player_grant": drawn,
            }))
            .is_ok(),
            "a grant nobody can recompute loads"
        );

        // The scoped derivable shape.
        assert!(
            refuse_derivable_player_grant(&serde_json::json!({
                "federation_id": federation_hex,
                "deployment_domain": DOMAIN,
                "player_grant": derivable_player_grant_cell_id(Some(DOMAIN), &federation_id),
            }))
            .is_err(),
            "the pre-flag-day descriptor must refuse to load"
        );

        // The UNSCOPED derivable shape: `auxiliary_genesis_key` with no domain is
        // `blake3::derive_key(context, b"genesis")` — one constant key for every
        // deployment that ever mints one, which is strictly worse.
        assert!(
            refuse_derivable_player_grant(&serde_json::json!({
                "federation_id": federation_hex,
                "player_grant": derivable_player_grant_cell_id(None, &federation_id),
            }))
            .is_err(),
            "a grant on the domainless constant key must refuse to load"
        );

        // Unreadable coordinates are refused, not skipped: a descriptor whose
        // custody CANNOT be checked does not get the benefit of the doubt.
        assert!(
            refuse_derivable_player_grant(&serde_json::json!({
                "player_grant": drawn,
            }))
            .is_err(),
            "a grant with no federation id cannot be custody-checked; refuse it"
        );
        assert!(
            refuse_derivable_player_grant(&serde_json::json!({
                "federation_id": "not-hex",
                "player_grant": drawn,
            }))
            .is_err(),
            "a grant with a malformed federation id cannot be custody-checked; refuse it"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deployment_domain_scopes_every_auxiliary_genesis_identity() {
        let federation_a = [0xA1; 32];
        let federation_b = [0xB2; 32];
        let domain = "pathofangels.network/federation/v1";
        for context in [
            "dregg-devnet-issuer-well-key-v1",
            "dregg-devnet-fee-well-key-v1",
            "dregg-devnet-faucet-key-v1",
        ] {
            let poa_a = auxiliary_genesis_key(context, Some(domain), &federation_a);
            let poa_b = auxiliary_genesis_key(context, Some(domain), &federation_b);
            let main = auxiliary_genesis_key(context, None, &federation_a);
            assert_ne!(poa_a, poa_b, "fresh federation ids must change {context}");
            assert_ne!(
                poa_a, main,
                "deployment-scoped {context} must not reuse legacy devnet"
            );
            assert_eq!(
                main,
                blake3::derive_key(context, b"genesis"),
                "the no-domain API preserves the existing devnet identity"
            );
        }
    }

    #[test]
    fn deployment_domains_are_length_delimited_from_federation_ids() {
        let federation = [0x11; 32];
        let a = auxiliary_genesis_key("dregg-devnet-fee-well-key-v1", Some("ab"), &federation);
        let b = auxiliary_genesis_key("dregg-devnet-fee-well-key-v1", Some("a"), &federation);
        assert_ne!(a, b, "domain bytes precede an explicit NUL delimiter");
    }

    #[test]
    fn default_starbridge_genesis_cells_has_six_apps_with_alice_owner() {
        let cells = default_starbridge_genesis_cells();
        assert_eq!(
            cells.len(),
            10,
            "devnet genesis must seed all starbridge app cells + the cap-inbox factory cell"
        );

        let labels: Vec<&str> = cells.iter().map(|c| c.label.as_str()).collect();
        assert!(labels.contains(&"nameservice-registry"));
        assert!(labels.contains(&"identity-issuer"));
        assert!(labels.contains(&"subscription-topic"));
        assert!(labels.contains(&"governed-namespace-root"));
        assert!(labels.contains(&"cwm-mandate"));
        assert!(labels.contains(&"sgm-gateway"));
        assert!(labels.contains(&"privacy-voting-poll"));
        assert!(labels.contains(&"privacy-voting-ballot"));
        assert!(labels.contains(&"bounty-board-bounty"));
        assert!(labels.contains(&"cap-inbox"));

        for cell in &cells {
            assert_eq!(cell.owner_agent, "alice");
            assert_eq!(
                cell.factory_vk_hex.len(),
                64,
                "factory_vk_hex must be 32 bytes"
            );
            assert!(
                !cell.uri_hint.is_empty(),
                "uri_hint must be set for {}",
                cell.label
            );
        }

        assert_eq!(
            cells[0].factory_vk_hex,
            hex_encode(&NAME_FACTORY_VK),
            "nameservice VK must match crate constant"
        );
    }

    #[test]
    fn genesis_config_serializes_starbridge_cells() {
        let config = GenesisConfig {
            federation_id: "aa".repeat(32),
            deployment_domain: None,
            committee_epoch: 0,
            consensus_genesis_unix_seconds: 1_700_000_000,
            consensus_time_mode: CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE,
            epoch_length: 100,
            checkpoint_interval: 10,
            validators: vec![],
            threshold: 1,
            initial_cells: vec![],
            issuer_well: "00".repeat(32),
            fee_well: "11".repeat(32),
            genesis_moves: vec![],
            player_grant: None,
            starbridge_cells: default_starbridge_genesis_cells(),
        };

        let json = serde_json::to_value(&config).expect("serialize genesis config");
        assert_eq!(json["consensus_genesis_unix_seconds"], 1_700_000_000);
        assert_eq!(
            json["consensus_time_mode"],
            CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE
        );
        let starbridge = json["starbridge_cells"]
            .as_array()
            .expect("starbridge_cells array present");
        assert_eq!(starbridge.len(), 10);
        assert_eq!(starbridge[0]["label"], "nameservice-registry");
        assert_eq!(starbridge[0]["owner_agent"], "alice");
        assert_eq!(starbridge[0]["uri_hint"], "registry-default");
    }

    /// THE GENESIS→BOOT SEAM: what `dregg-node genesis` writes is what the
    /// running node materializes, and the result is a faucet cell that can
    /// actually ACT.
    ///
    /// Both halves failed silently before 2026-07-25: genesis minted every cell
    /// in the all-zero asset (so `validate_signed_turn` — which requires
    /// `agent == derive_raw(signer, blake3("default"))` — refused every turn
    /// those cells were the agent of), and no cell committed a PQ identity (so
    /// required-PQ admission refused them a second time). Neither refusal was
    /// visible at the faucet's HTTP boundary; both landed at FINALIZATION, after
    /// `success: true`.
    #[test]
    fn generated_genesis_materializes_a_faucet_cell_that_can_act() {
        let tmp = tempfile::tempdir().expect("tempdir");
        run_genesis(1, 1000, 100, tmp.path());
        let genesis: serde_json::Value =
            serde_json::from_slice(&std::fs::read(tmp.path().join("genesis.json")).expect("read"))
                .expect("genesis.json parses");

        let mut ledger = dregg_cell::Ledger::new();
        let stats = crate::materialize_genesis_cells_for_test(&genesis, &mut ledger);
        assert_eq!(stats, (6, 0), "6 genesis cells inserted, none invalid");

        // Replay the issuer-moves the way boot does, then check the faucet.
        let faucet_id = devnet_faucet_cell_id();
        let faucet = ledger
            .get(&faucet_id)
            .expect("the faucet cell genesis mints must be the one `POST /api/faucet` spends from");
        assert_eq!(
            *faucet.asset().as_bytes(),
            crate::executor_setup::default_token_id(),
            "the faucet must hold the canonical default asset"
        );
        assert_eq!(
            faucet.id(),
            dregg_cell::CellId::derive_raw(
                faucet.public_key(),
                &crate::executor_setup::default_token_id()
            ),
            "and its id must be the signer's default cell — the only shape a turn agent may take"
        );
        let identity = faucet
            .pq_identity()
            .expect("the faucet cell must COMMIT its ML-DSA identity or hybrid admission refuses");
        let expected = dregg_cell::ml_dsa_public_key_commitment(&ml_dsa_public_key_for_seed(
            &blake3::derive_key("dregg-devnet-faucet-key-v1", b"genesis"),
        ))
        .expect("canonical ML-DSA-65 key");
        assert_eq!(
            identity.ml_dsa_key_commitment, expected,
            "the committed identity must be the key the faucet cipherclerk signs with"
        );

        // The issuer well is in the same asset, so its moves are single-column.
        let well = ledger
            .get(&devnet_issuer_well_id())
            .expect("issuer well materializes");
        assert_eq!(
            well.asset(),
            faucet.asset(),
            "well and holders must share one asset column (guarantee B's genesis hypothesis)"
        );
    }

    #[test]
    fn every_node_env_uses_the_same_persisted_consensus_time_anchor() {
        let anchor = 1_700_000_000;
        let a = node_env_content(0, 2, &["node-1:9420".into()], anchor);
        let b = node_env_content(1, 2, &["node-0:9420".into()], anchor);
        let coordinate = format!("{CONSENSUS_GENESIS_UNIX_SECONDS_ENV}={anchor}\n");
        assert!(a.contains(&coordinate));
        assert!(b.contains(&coordinate));
        let mode = format!("{CONSENSUS_TIME_V1_MODE_ENV}={CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE}\n");
        assert!(a.contains(&mode));
        assert!(b.contains(&mode));
    }
}
