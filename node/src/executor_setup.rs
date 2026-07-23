//! Blocklace-aware [`TurnExecutor`] configuration shared across node entry points.
//!
//! Keeps federation id, wall-clock timestamp, and attested block height aligned with
//! the same rules as [`crate::blocklace_sync::execute_finalized_turn`].

use std::sync::Arc;
use std::sync::OnceLock;

use dregg_circuit::dsl::circuit::CellProgram;
use dregg_circuit::dsl::dfa_routing::dfa_routing_descriptor;
use dregg_dsl_runtime::ProgramRegistry;
use dregg_turn::TurnExecutor;
use dregg_turn::executor::DslCircuitDfaVerifier;

use crate::state::NodeStateInner;

/// The deployed name of the node's routing circuit — the `dregg-dfa-routing-v1`
/// route-commitment-binding AIR (`dregg_circuit::dsl::dfa_routing`, faithful to
/// the Lean model `Dregg2.Crypto.DfaAcceptanceAir`).
pub const ROUTE_CIRCUIT_NAME: &str = "dregg-dfa-routing-v1";

/// The node's canonical 4-state message router, flattened to `(state, symbol, next)`.
///
/// States: `IDLE=0`, `LOCAL=1`, `REMOTE=2`, `REJECT=3`.
/// Symbols: `internal=0`, `external=1`, `privileged=2`, `unknown=3`.
///
/// This is the SAME table the `dregg-dfa-routing-v1` AIR was authored and proven
/// against (`circuit/src/dsl/dfa_routing.rs` `tests::router_transitions`, and the
/// `live_routing*` teeth in `turn/src/executor/membership_verifier.rs`). The table
/// is the routing POLICY: its `compute_table_commitment` seeds every route
/// commitment, and it flows into the descriptor — so changing it changes
/// [`route_circuit_vk`], which is a deliberate, visible re-deployment.
pub fn canonical_router_transitions() -> Vec<(u32, u32, u32)> {
    // TRANSITIONS = [[1,2,1,3],[1,2,1,3],[1,2,3,3],[3,3,3,3]]
    let table = [[1, 2, 1, 3], [1, 2, 1, 3], [1, 2, 3, 3], [3, 3, 3, 3]];
    let mut out = Vec::new();
    for (state, row) in table.iter().enumerate() {
        for (symbol, &next) in row.iter().enumerate() {
            out.push((state as u32, symbol as u32, next));
        }
    }
    out
}

/// The node's deployed routing program.
///
/// No ceremony, no epoch decision: a DSL program's `vk_hash` is CONTENT-DERIVED
/// (`CellProgram::compute_vk_hash` = blake3 over the postcard-serialized
/// descriptor), so this program's identity follows from the descriptor + the
/// canonical table alone — every node that runs this code mints the same vk.
pub fn route_circuit_program() -> &'static CellProgram {
    static PROGRAM: OnceLock<CellProgram> = OnceLock::new();
    PROGRAM.get_or_init(|| {
        CellProgram::new(
            dfa_routing_descriptor(ROUTE_CIRCUIT_NAME, &canonical_router_transitions()),
            1,
        )
    })
}

/// The routing circuit's verification-key hash — the commitment a relay's
/// `Witnessed { Dfa }` caveat carries (the relay's `route_table_root`).
///
/// [`DslCircuitDfaVerifier`] resolves a Dfa caveat's commitment against the
/// deployed [`ProgramRegistry`]; a `vk_hash` absent from it fails closed. This is
/// the vk under which [`configure_turn_executor`] deploys the routing program, so
/// a Dfa caveat carrying it now DISCHARGES through the real STARK verifier
/// instead of being rejected as `KindNotRegistered`.
pub fn route_circuit_vk() -> [u8; 32] {
    route_circuit_program().vk_hash
}

/// The registry the node's `Dfa` verifier resolves against: exactly the pinned
/// routing circuit at [`route_circuit_vk`].
///
/// Caller-deployed custom programs live in `NodeStateInner::program_registry`
/// and are copied to `TurnExecutor::program_registry` for custom cell-program
/// verification. They must never enter this route-policy registry.
pub fn program_registry_with_route_circuit(_s: &NodeStateInner) -> ProgramRegistry {
    // A FRESH registry holding EXACTLY the canonical route circuit — deliberately
    // NOT `s.program_registry`.
    //
    // `DslCircuitDfaVerifier` resolves ANY `vk_hash` present in the registry it is
    // handed, lowers that program, and verifies its STARK against PROVER-SUPPLIED
    // public inputs; nothing else pins the program to the routing circuit. The
    // node's `s.program_registry` is CALLER-FILLABLE: `POST /programs/deploy`
    // (`api.rs::post_deploy_program`) accepts an arbitrary postcard
    // `CircuitDescriptor` and `descriptor.validate()` has no minimum-constraint
    // check, so a trivially-satisfiable program sails through. (That route sits
    // behind `require_auth`, so this is "any AUTHORIZED deployer", not "anyone" —
    // but that is exactly the point: the Dfa verifier must not trust a circuit
    // merely because some authorized caller deployed it. Defence in depth.)
    // Handing that registry to the verifier would let such a deployer and
    // discharge a `Dfa` caveat against their OWN program's vk — turning a
    // fail-closed (safe-but-dead) relay into a live forgery surface. Pinning the
    // registry to the one content-derived route vk is what makes wiring the
    // verifier an improvement rather than a regression.
    let mut programs = ProgramRegistry::new();
    // `deploy` only fails on a descriptor that does not validate or a vk_hash that
    // does not match its descriptor — neither is possible for a `CellProgram::new`
    // over the pinned descriptor (`descriptor_is_deployable` pins the validation).
    programs
        .deploy(route_circuit_program().clone())
        .expect("the canonical dregg-dfa-routing-v1 program must deploy");
    programs
}

/// How to derive the executor's block height from node state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockHeightMode {
    /// Use the latest attested root height (read-only / verify paths).
    Current,
    /// Use `latest + 1` — the height assigned to the turn about to execute.
    Next,
}

/// Resolve the blocklace-attested height from persistent store + solo fallback.
pub fn attested_block_height(s: &NodeStateInner) -> u64 {
    let store_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let solo_height = s
        .solo_consensus
        .as_ref()
        .map(|solo| solo.height)
        .unwrap_or(0);
    store_height.max(solo_height)
}

/// Federation id for turn signing — matches blocklace finalized-turn path.
pub fn federation_id_for_executor(s: &NodeStateInner) -> [u8; 32] {
    if s.federation_configured {
        s.federation_id
    } else {
        *blake3::hash(s.cclerk.public_key().as_bytes()).as_bytes()
    }
}

fn wall_clock_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

fn cached_local_ml_dsa_public(seed: &[u8; 32], ed25519: [u8; 32]) -> Vec<u8> {
    // Executors are intentionally short-lived, while identity keys are not.
    // Cache only the PUBLIC ML-DSA bytes by the already-public Ed25519 identity;
    // never retain the seed in this process-global map. Two racing first calls
    // may both derive, but the installed value is identical.
    static CACHE: OnceLock<std::sync::Mutex<std::collections::HashMap<[u8; 32], Vec<u8>>>> =
        OnceLock::new();
    let cache = CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Some(public_key) = cache
        .lock()
        .expect("local PQ identity cache mutex poisoned")
        .get(&ed25519)
        .cloned()
    {
        return public_key;
    }

    let public_key = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(seed).public_bytes();
    cache
        .lock()
        .expect("local PQ identity cache mutex poisoned")
        .entry(ed25519)
        .or_insert_with(|| public_key.clone())
        .clone()
}

/// Install every target-cell ML-DSA identity the node knows independently of
/// the turn currently being checked.
///
/// Two host-anchored sources exist today:
///
/// - cells owned by this node's cipherclerk use the ML-DSA key derived from the
///   clerk's locally held seed;
/// - cells owned by a configured federation member use the ML-DSA key published
///   beside that member's Ed25519 key in the genesis/committee roster.
///
/// Nothing is learned from `Authorization::HybridSignature::ml_dsa_pk`. An
/// external user cell absent from these enrolled sources therefore fails closed
/// under native/required PQ. The classical-only posture is an explicitly
/// unaudited test/development mode, not a deployment or migration profile.
pub fn enroll_known_pq_identities(executor: &TurnExecutor, s: &NodeStateInner) {
    let local_seed = s.cclerk.gossip_signing_key().to_bytes();
    let local_ed25519 = s.cclerk.public_key().0;
    // The explicitly unaudited classical test mode must remain usable in a
    // marshal-only process: merely constructing an executor must not invoke
    // dregg-pq's fail-closed unaudited fallback. Native deployments install the
    // verified keygen core before serving; test/development fallback is possible
    // only under the same explicit opt-in enforced by dregg-pq itself.
    let local_keygen_available = dregg_pq::lean_keygen_core_real_installed()
        || std::env::var(dregg_pq::ALLOW_UNAUDITED_PQ_ENV).as_deref() == Ok("1");
    // Lazy: read-only verifier executors over an empty/non-local ledger need no
    // local identity and therefore must not invoke keygen merely by existing.
    // A real locally owned target pays this once while the executor is built.
    let mut local_ml_dsa: Option<Vec<u8>> = None;

    for (cell_id, cell) in s.ledger.iter() {
        let target_ed25519 = *cell.public_key();
        let enrolled_key = if target_ed25519 == local_ed25519 && local_keygen_available {
            Some(
                local_ml_dsa
                    .get_or_insert_with(|| cached_local_ml_dsa_public(&local_seed, local_ed25519))
                    .clone(),
            )
        } else {
            s.ml_dsa_key_for(&target_ed25519).map(|key| key.0.to_vec())
        };

        if let Some(enrolled_key) = enrolled_key {
            // Every source above has a fixed-size ML-DSA key and each target is
            // visited once, so an error means host configuration is internally
            // contradictory. Do not silently run a "required" executor with a
            // missing identity: fail at configuration time.
            executor
                .enroll_pq_identity(
                    *cell_id,
                    target_ed25519,
                    cell.state.delegation_epoch(),
                    enrolled_key,
                )
                .expect("host-anchored PQ identity enrollment must be coherent");
        }
    }
}

/// Configure `executor` with federation id, timestamp, and blocklace height.
pub fn configure_turn_executor(
    executor: &mut TurnExecutor,
    s: &NodeStateInner,
    height_mode: BlockHeightMode,
) {
    // `NoteSpend` is a hard predicate-specific HidingFRI path.  Install its
    // verifier on every production executor: the predicate-less entry refuses,
    // and the named entry accepts only the exact Lean-emitted v2 relation and
    // fixed 44-felt statement reconstructed by the executor.
    // (The verifier moved to `dregg-turn-prover` with the prover-crate extraction: core
    // `dregg-turn` no longer links `dregg-circuit-prove`, so the concrete HidingFRI
    // verifier lives on the prover side and the node injects it here.)
    executor.set_proof_verifier(Box::new(dregg_turn_prover::FaithfulNoteSpendVerifier::new()));

    // The spent-note accumulator is durable finalized state, not executor-local
    // scratch.  Every short-lived production executor must begin at that exact
    // frontier or a restart (and, before this weld, every ordinary submit after
    // the first finalized spend) forgets prior nullifiers and evaluates the next
    // FNSP successor against an empty set.  That both breaks honest cross-turn
    // proving and weakens the executor's early double-spend refusal.
    //
    // Corrupt/gapped durable records are a store-integrity event.  Refuse to
    // construct an admission executor rather than silently substituting the
    // empty accumulator: an empty fallback is precisely the unsafe state.
    let durable_nullifier_records =
        s.store
            .load_faithful_nullifier_records()
            .unwrap_or_else(|error| {
                panic!(
                    "STORE INTEGRITY EVENT: could not load finalized faithful nullifiers; \
                 refusing to construct a turn executor: {error}"
                )
            });
    let durable_nullifier_set =
        dregg_cell::nullifier_set::NullifierSet::from_records(durable_nullifier_records)
            .unwrap_or_else(|error| {
                panic!(
                    "STORE INTEGRITY EVENT: finalized faithful nullifier sequence is malformed; \
                     refusing to construct a turn executor: {error}"
                )
            });
    *executor.note_nullifiers.lock().unwrap() = durable_nullifier_set;

    // The remaining grow-only executor accumulators are equally consensus
    // state. Restore the complete typed records (including value/height and
    // append sequence) plus the inbound bridge replay gate before any request
    // executes. The helper constructs every successor first and publishes all
    // three together, so corruption cannot partially seed the fresh executor.
    crate::executor_side_state_persistence::restore_executor_accumulators(executor, &s.store)
        .unwrap_or_else(|error| {
            panic!(
                "STORE INTEGRITY EVENT: could not restore executor commitment/revocation/bridge \
                 state; refusing to construct a turn executor: {error}"
            )
        });

    crate::executor_side_state_persistence::restore_executor_rate_limits(executor, &s.store)
        .unwrap_or_else(|error| {
            panic!(
                "STORE INTEGRITY EVENT: durable rate-limit state cannot seed a turn executor; \
                 refusing construction: {error}"
            )
        });

    crate::executor_side_state_persistence::restore_executor_factory_registry(executor, &s.store)
        .unwrap_or_else(|error| {
            panic!(
                "STORE INTEGRITY EVENT: durable factory-registry state cannot seed a turn \
                 executor; refusing construction: {error}"
            )
        });

    crate::executor_side_state_persistence::restore_executor_reactive_state(executor, &s.store)
        .unwrap_or_else(|error| {
            panic!(
                "STORE INTEGRITY EVENT: durable pending registry/React replay state cannot seed a \
                 turn executor; refusing construction: {error}"
            )
        });

    // Receipt-chain continuity is consensus state too. Node executors are
    // short-lived, so restoring only the one agent an ingress happens to name
    // leaves every other author at a false genesis head. Rebuild all per-agent
    // heads from the already recovered durable log before any execution. The
    // helper validates the complete interleaved log before mutating the fresh
    // executor, so a malformed suffix cannot yield a partially seeded view.
    crate::executor_state_admission::restore_executor_receipt_heads(
        executor,
        s.cclerk.receipt_log(),
    )
    .unwrap_or_else(|error| {
        panic!(
            "STORE INTEGRITY EVENT: durable receipt log cannot seed a turn executor; refusing construction: {error}"
        )
    });

    // Generic touched-cell provenance is not derivable from the receipt log:
    // the write set lives in commit records, and compaction removes old records.
    // Restore the validated compacted-baseline + live-suffix projection before
    // any atomic/mixed path asks for a cell's predecessor receipt.
    crate::executor_state_admission::restore_executor_per_cell_receipt_heads(executor, &s.store)
        .unwrap_or_else(|error| {
            panic!(
                "STORE INTEGRITY EVENT: durable per-cell receipt heads cannot seed a turn executor; refusing construction: {error}"
            )
        });

    // Custom cell-program verification resolves the program VK committed by a
    // cell against the node's durable deployed-program registry. Executors are
    // short-lived, so leaving the constructor default (empty) would make every
    // deployed program disappear at the next submit/verify boundary. This is a
    // distinct registry from the Dfa verifier below: arbitrary caller-deployed
    // programs are valid application code, but never trusted route policy.
    executor.set_program_registry(s.program_registry.clone());

    executor.set_local_federation_id(federation_id_for_executor(s));
    executor.set_timestamp(wall_clock_secs());
    enroll_known_pq_identities(executor, s);
    // Sign committed receipts with the node's key (same key the MCP entry
    // points use). Without this, every HTTP/blocklace-path receipt carried
    // `executor_signature: None` (`executor_signed:false` in /api/receipts) and
    // conditional-turn verification of our receipts was impossible.
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());

    // ORGANS §5 (adjudication): install the court's `validEquivocation`
    // predicate atom into the executor's witnessed-predicate registry, so
    // turn admission / cell programs can gate on a verified fork exhibit
    // (CONSENSUS-FLEX §7 item 2, live on every node executor).
    if let Some(registry) = executor.witnessed_registry.as_mut() {
        dregg_federation::court::register_equivocation_court(registry);

        // DFA ROUTE-COMMITMENT (the relay's caveat): install the real
        // `DslCircuitDfaVerifier` over ONLY the canonical routing circuit. The
        // executor default
        // (`registry_with_real_verifiers`) leaves `Dfa` FAIL-CLOSED because the
        // kind needs a host-trusted `ProgramRegistry`; this supplies it, so a
        // relay's `Witnessed { Dfa }` caveat carrying `route_circuit_vk()` now
        // discharges through the real route-commitment-binding STARK ("a router
        // cannot claim a delivery it did not make") instead of being rejected
        // before its verify logic runs. This upgrades ONLY `Dfa` — every other
        // kind stays exactly as `registry_with_real_verifiers` set it. A caveat
        // whose commitment is NOT a deployed vk_hash still fails closed.
        registry.register_builtin(Arc::new(DslCircuitDfaVerifier::new(Arc::new(
            program_registry_with_route_circuit(s),
        ))));
    }

    // THE EPOCH §5 (signed wells): wire the genesis-declared wells so fees
    // are MOVES to the fee well and Burn is a MOVE to the asset's issuer
    // well — every committed turn conserves exactly
    // (`reachable_total_zero`'s hypotheses hold on the deployed chain).
    if let Some(fee_well) = s.fee_well {
        executor.set_fee_well_cell(fee_well);
    }
    for (token_id, well) in &s.issuer_wells {
        executor.register_issuer_well(*token_id, *well);
    }

    // COORDINATION-TURN CLASS ("leash, not ledger"): genesis-declared opt-in
    // (`genesis.json` `coordination_fee_exempt` → NodeState). EmitEvent-only
    // turns with no `balance_change` may carry `fee = 0` — the executor waives
    // the CHARGE while the receipt's `computrons_used` stays honest. Default
    // off: zero behavior change unless a deployment opts in at genesis.
    executor.costs.coordination_exempt = s.coordination_fee_exempt;

    let base = attested_block_height(s);
    let height = match height_mode {
        BlockHeightMode::Current => base,
        BlockHeightMode::Next => base.saturating_add(1),
    };
    executor.set_block_height(height);
}

/// THE default asset (token domain) of this node's chain: `blake3("default")`.
///
/// This is the ONE domain that has to hold for a cell to be able to ACT: the
/// single application-admission predicate
/// (`signed_turn_validation::validate_signed_turn`) requires
/// `turn.agent == CellId::derive_raw(signer, blake3("default"))`, and it runs at
/// HTTP ingress, at finalized-block execution, and in the PostgreSQL drainer. A
/// cell minted in any other domain is unspendable-by-its-owner: its owner's
/// signature can never authorize a turn whose agent is that cell.
///
/// It is therefore also the asset genesis mints into (`genesis.rs`) and the one
/// the faucet transfers (`api.rs`). Before 2026-07-25 those two used `[0u8; 32]`
/// while the predicate used `blake3("default")` — a split asset namespace whose
/// visible symptom was a faucet that answered `success: true` and moved nothing.
///
/// # A CELL THAT PAYS A FEE MUST LIVE HERE
///
/// `blake3("default")` is not "an asset". It is the asset in which AGENCY is
/// denominated, and two independent rules now say so:
///
/// * the admission predicate above (`agent == derive_raw(signer, default)`); and
/// * fees. THE EPOCH §5 makes a fee a MOVE to the fee well, and since
///   `94f4d7f123` a `Transfer` is a single-asset move (`apply.rs`, welded to the
///   kernel's `recTransferBal`). A cell in a private asset therefore cannot be
///   funded by the operator, and cannot pay a fee into a default-asset fee well.
///
/// THE TRAP THIS LEAVES. `dregg_cell::Cell`'s `token_id` does TWO jobs at once:
/// it is the cell's ASSET, and it is the namespace salt in
/// `CellId::derive_raw(owner_pubkey, token_id)`. Every app that needs one cell
/// per (owner, tag) reaches for the only free axis and gets a private currency it
/// never asked for — `channels_service::channel_token_id`,
/// `dkg_service::dkg_ceremony_token_id`, `trustline_service`'s per-line hash,
/// `equivocation_court_service`'s `BOND_CELL_DOMAIN` / `SLASH_SINK_DOMAIN`. Those
/// helpers are NAMES, not currencies, and the cells they mint hold computrons, so
/// the create-then-fund pattern they all share is refused `cross-asset Transfer
/// rejected` at the executor. That refusal is CORRECT; the pattern is not legal.
///
/// The migration is "stop minting acting cells in a private asset", and it is not
/// free: the owner side of the derivation cannot absorb the tag either (the adopt
/// turn authorizes against the cell's `public_key`, so it has to be a real key).
/// The honest options are (a) split `Cell.token_id` into `asset` + `name_salt` —
/// correct, and a Cell wire change plus a store migration; or (b) remove the need
/// for those cells to hold computrons at all (sponsored fees, so the operator's
/// cell pays for a turn whose agent is the app cell). Neither is a test edit.
pub fn default_token_id() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

/// The node's OWN agent cell — `derive_raw(cipherclerk pubkey, blake3("default"))`. This is the
/// agent whose receipt chain the cipherclerk maintains authoritatively (the source of the
/// host-fed `stored_head` for the boundary-P1 admission shadow). Mirrors the derivation in
/// `api.rs` (the submit path), centralised so the blocklace-finalized path agrees.
pub fn local_agent_cell(s: &NodeStateInner) -> dregg_cell::CellId {
    dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &default_token_id())
}

/// THE one executor gate (#171): execute `turn` through the producer-aware path
/// shared by EVERY ingress — the thin-HTTP `/turn/submit`, the signed-envelope
/// `/turns/submit` (remote agents), and blocklace-finalized turns all call this,
/// so a remote-submitted turn runs on exactly the same authoritative state
/// producer as a local one (no parallel entry).
///
/// THE SWAP — producer mode (authority inversion), the DEFAULT. When
/// `lean_producer_enabled` is set (default ON unless `DREGG_LEAN_PRODUCER=0`),
/// the VERIFIED Lean executor is the authoritative state PRODUCER for the
/// swap-safe COVERED set: `produce_via_lean` reconstitutes the committed ledger
/// from the Lean FFI's post-state and demotes the Rust `TurnExecutor` to a
/// parallel differential cross-check, returning the Rust `TurnResult` (so the
/// receipt / proving / attestation machinery is unchanged) together with a
/// differential outcome. A turn that is unmappable or touches a characterized
/// root-gap effect falls back to the Rust producer for that turn (logged, never
/// silent). A covered-set divergence keeps the Rust state and is surfaced as a
/// real soundness finding. When the flag is OFF, this is exactly the legacy
/// Rust-producer path.
pub fn execute_via_producer(
    executor: &TurnExecutor,
    turn: &dregg_turn::Turn,
    ledger: &mut dregg_cell::Ledger,
    lean_producer_enabled: bool,
) -> dregg_turn::TurnResult {
    use tracing::{error, info, warn};

    // Exact FNSP-v3 currently owns one proof-local subreceipt joined to one
    // genuine full-turn receipt. Until every mutable executor side table has a
    // durable node-owned reconstruction, composing an exact spend with another
    // effect would let the latter mutate state outside that staged exact frame.
    // Refuse before the Rust or Lean producer touches either ledger or side
    // tables; the consequence must be a separately finalized outbox turn.
    if let Err(route_error) =
        crate::executor_state_admission::validate_exact_fnsp_v3_route(turn, ledger)
    {
        return dregg_turn::TurnResult::Rejected {
            reason: dregg_turn::TurnError::InvalidEffect {
                reason: format!("exact FNSP-v3 route refused: {route_error}"),
            },
            at_action: Vec::new(),
        };
    }

    // The verified Lean producer does not yet project the exact FNS3,
    // commitment, or revocation side accumulators. Its generic root-agreement
    // classifier therefore cannot author this exact route without silently
    // dropping consensus state. Keep the staged exact epoch on the Rust
    // producer after the strict fence until that projection is implemented and
    // differentially pinned.
    if crate::executor_state_admission::is_strict_exact_fnsp_v3_route(turn) {
        warn!(
            agent = ?turn.agent,
            "exact FNSP-v3 route is fenced onto the Rust producer until Lean projects executor side-state roots"
        );
        return executor.execute(turn, ledger);
    }

    if !lean_producer_enabled {
        return executor.execute(turn, ledger);
    }

    let agent = turn.agent;
    let (result, outcome) = dregg_exec_lean::produce_via_lean(executor, turn, ledger);
    match &outcome {
        dregg_exec_lean::ProducerOutcome::LeanAuthoritative {
            committed,
            rust_agreed,
            divergence,
            lean_root,
            rust_root,
            rust_committed,
        } => {
            if *rust_agreed {
                info!(
                    target: "dregg::lean_shadow::producer",
                    agent = ?agent,
                    committed = *committed,
                    "THE SWAP producer mode: verified Lean executor is AUTHORITATIVE for this \
                     covered turn (its post-state is committed); Rust reference AGREES"
                );
            } else {
                // THE AUTHORITY INVERSION's tooth: on a covered turn a Lean↔Rust disagreement is,
                // by definition, the Rust path being WRONG (Rust is the artifact dregg2 replaces
                // because it is buggy). The verified Lean verdict was committed; this surfaces the
                // Rust bug as a finding — it is NOT a fallback to Rust.
                error!(
                    target: "dregg::lean_shadow::producer",
                    agent = ?agent,
                    lean_committed = *committed,
                    rust_committed = *rust_committed,
                    // WHICH leg caught it (`ProducerDivergence`): `CommitBit` = the two executors
                    // disagreed on committing at all; `Anchor` = same verdict, different signed
                    // consensus commitment; `PostStateCell` = both agree on the verdict AND the
                    // anchor, and the ledgers still differ at a cell the anchor is structurally
                    // blind to. Logging only the two roots could not tell those apart, and for a
                    // `PostStateCell` finding it printed two IDENTICAL roots beside "DISAGREE".
                    divergence = ?divergence,
                    lean_root = %dregg_types::hex_encode(lean_root),
                    rust_root = %dregg_types::hex_encode(rust_root),
                    "THE SWAP authority inversion: verified Lean executor (AUTHORITATIVE) and the \
                     demoted Rust reference DISAGREE on a covered turn — the Rust path is BUGGY \
                     (REAL finding). The verified Lean verdict was committed; Rust was NOT \
                     allowed to override it"
                );
            }
        }
        dregg_exec_lean::ProducerOutcome::Fallback { reason } => {
            warn!(
                target: "dregg::lean_shadow::producer",
                agent = ?agent,
                reason = %reason,
                "THE SWAP producer mode: turn outside the swap-safe covered set — FENCED onto the \
                 legacy Rust path for this turn (explicit, surfaced; the named burning-down \
                 partition, not a silent Rust-authoritative default)"
            );
        }
    }
    result
}

/// COMMIT ARBITRARY EFFECTS AS `agent` — the factored core of the signed-turn
/// commit path, callable WITHOUT an HTTP envelope.
///
/// The signed-turn ingress (`api.rs::post_submit_signed_turn`) verifies a caller
/// signature, derives the agent, then runs exactly this core: build a `Turn`
/// carrying `effects` under `agent`'s current nonce + chain head, execute it
/// through the ONE producer gate (`execute_via_producer`), and append the
/// committed `TurnReceipt` to the cipherclerk chain. This helper is that core,
/// without the signature/HTTP/gossip/proving shell — so an IN-PROCESS host (the
/// `deos-host` server program, which owns the agent cell and decides its effects
/// directly) commits a real verified turn on the node's ledger by the same path.
///
/// Returns the committed receipt hash, or a rejection reason. The receipt lands
/// on `s.cclerk`'s chain and the ledger is mutated in place — identical to the
/// HTTP path's committed-turn semantics, minus the wire shell.
// In-process committed-turn entry mirroring the HTTP path; reached via tests / the deos-host program.
pub fn commit_effects_as(
    s: &mut crate::state::NodeStateInner,
    agent: dregg_cell::CellId,
    method: &str,
    effects: Vec<dregg_turn::action::Effect>,
) -> Result<[u8; 32], String> {
    use dregg_turn::{CallForest, Turn};

    let exec_federation_id = federation_id_for_executor(s);
    let nonce = s.ledger.get(&agent).map(|c| c.state.nonce()).unwrap_or(0);
    // `agent`'s OWN causal head. `receipt_chain()` is the node-WIDE observation log,
    // which interleaves every agent this node ever committed for; both gates this turn
    // passes are agent-scoped — `TurnExecutor::check_previous_receipt_hash` against the
    // per-agent map `configure_turn_executor` restores from the same log, and
    // `AgentCipherclerk::append_receipt`'s own `agent_receipt_head_hash` check on the way
    // out. Stamping the wide head made `commit_effects_as` reject with `receipt chain
    // mismatch` from the first moment any OTHER agent (the faucet, every newcomer's first
    // step) committed.
    let prev = s.cclerk.agent_receipt_head_hash(&agent);

    // Signed over `nonce` — the value THIS turn carries, read from `agent`'s own
    // ledger cell — because `dregg-action-sig-v3` binds the turn nonce into the
    // canonical action signing message and the executor re-derives it as
    // `compute_signing_message(action, federation_id, turn.nonce)`. The
    // convenience `make_action` signs over the clerk's `next_turn_nonce()`
    // instead: the receipt count of the clerk's DEFAULT agent, i.e. the operator
    // cell, whoever `agent` happens to be. Those two are the same number only
    // while `agent` IS the operator and every one of its turns committed, so
    // this entry refused any other agent with `hybrid: Ed25519 (classical)
    // signature half failed` the moment the operator's chain had moved. Same
    // footgun `api.rs`'s faucet path closed in `0329df216` and
    // `trustline_service::run_signed_turn` in this one.
    let action = s.cclerk.sign_action_hybrid(
        dregg_sdk::raw::unsigned_action_named(agent, method, effects),
        &exec_federation_id,
        nonce,
    );
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);

    let mut turn = Turn {
        agent,
        nonce,
        fee: 0,
        memo: Some(format!("deos_host:{method}")),
        valid_until: Some(i64::MAX / 2),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash: prev,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let executor = new_submit_executor(s);
    // Size the fee to the estimated computron cost so the executor budget gate passes.
    turn.fee = executor.estimate_cost(&turn);

    let lean_producer_enabled = s.lean_producer_enabled;
    match execute_via_producer(&executor, &turn, &mut s.ledger, lean_producer_enabled) {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let rh = receipt.receipt_hash();
            s.cclerk
                .append_receipt(receipt)
                .map_err(|e| format!("append_receipt: {e}"))?;
            Ok(rh)
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => Err(format!("rejected: {reason}")),
        other => Err(format!("turn did not commit: {other:?}")),
    }
}

/// Build a fresh executor configured for turn submission (height = attested + 1).
///
/// The verified-Lean shadow/gate observer (`dregg_exec_lean::LeanShadowObserver`) is injected
/// UNCONDITIONALLY on the native node — the differential cross-check and the strict-veto rejection
/// authority are live on every executor the node builds. (Only a wasm / no-FFI build, which does
/// not depend on `dregg-exec-lean`, gets the no-op default.)
pub fn new_submit_executor(s: &NodeStateInner) -> TurnExecutor {
    let mut executor = TurnExecutor::new(dregg_turn::ComputronCosts::default())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc());
    configure_turn_executor(&mut executor, s, BlockHeightMode::Next);
    require_pq_admission(&executor);
    executor
}

fn pq_admission_required(require_pq: Option<&str>, allow_unaudited_pq: Option<&str>) -> bool {
    let classical_requested = require_pq
        .map(|v| v == "0" || v.eq_ignore_ascii_case("false"))
        .unwrap_or(false);
    let unaudited_test_mode = allow_unaudited_pq == Some("1");
    !(classical_requested && unaudited_test_mode)
}

/// HYBRID PERIMETER — DEPLOYED POSTURE (require_pq = ON) at the ADMISSION
/// boundary. Called on the executors the node uses to ADMIT a turn for commit:
/// the thin-HTTP + signed-envelope submit path (`new_submit_executor`, reached by
/// `commit_effects_as` and the queue drainers too) and the blocklace
/// finalized-turn path (`blocklace_sync::execute_finalized_turn`). Requiring the
/// post-quantum half rejects a classical-only `Authorization::Signature` and an
/// outer envelope lacking a PQ signature (`api.rs::post_submit_signed_turn` reads
/// `require_pq()`); a present hybrid `HybridSignature` (ed25519 + ML-DSA-65) is
/// accepted only when its ML-DSA key matches the independently enrolled target
/// cell identity/epoch installed by [`enroll_known_pq_identities`]. The Rust
/// default signer and both SDKs emit the hybrid shape, while external identities
/// still require a durable enrollment before they can use native-PQ admission.
/// NOT applied to `new_verify_executor`: read/proof
/// re-execution replays turns already admitted (possibly pre-flip classical
/// history), so gating it on PQ presence would wrongly reject a legitimate read.
/// A present-but-invalid PQ half is fail-closed in EITHER mode regardless.
///
/// DEPLOYED DEFAULT is unconditionally ON. Classical authorization exists only
/// as an explicitly UNAUDITED test/development posture: it requires BOTH
/// `DREGG_REQUIRE_PQ=0` (or `false`) and `DREGG_ALLOW_UNAUDITED_PQ=1`. The first
/// variable alone never downgrades a native node.
pub fn require_pq_admission(executor: &TurnExecutor) {
    let require_pq = std::env::var("DREGG_REQUIRE_PQ").ok();
    let allow_unaudited_pq = std::env::var(dregg_pq::ALLOW_UNAUDITED_PQ_ENV).ok();
    executor.set_require_pq(pq_admission_required(
        require_pq.as_deref(),
        allow_unaudited_pq.as_deref(),
    ));
}

/// Build a fresh executor at the current attested height (verify / read paths). Injects the
/// verified-Lean shadow/gate observer like [`new_submit_executor`].
pub fn new_verify_executor(s: &NodeStateInner) -> TurnExecutor {
    let mut executor = TurnExecutor::new(dregg_turn::ComputronCosts::default())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc());
    configure_turn_executor(&mut executor, s, BlockHeightMode::Current);
    executor
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn height_mode_next_increments() {
        let base = 41u64;
        let next = match BlockHeightMode::Next {
            BlockHeightMode::Next => base.saturating_add(1),
            BlockHeightMode::Current => base,
        };
        assert_eq!(next, 42);
    }

    #[test]
    fn native_pq_never_downgrades_without_double_explicit_unaudited_test_mode() {
        assert!(pq_admission_required(None, None));
        assert!(pq_admission_required(Some("0"), None));
        assert!(pq_admission_required(Some("false"), Some("true")));
        assert!(pq_admission_required(Some("1"), Some("1")));
        assert!(!pq_admission_required(Some("0"), Some("1")));
        assert!(!pq_admission_required(Some("FALSE"), Some("1")));
    }

    /// `commit_effects_as` is the in-process committed-turn entry the `deos-host`
    /// program uses. It stamped `previous_receipt_hash` from
    /// `cclerk.receipt_chain().last()` — the node-WIDE observation log head — while
    /// both gates the turn then has to pass are agent-scoped: the executor's
    /// `check_previous_receipt_hash` against the per-agent map
    /// `configure_turn_executor` restores from that same log, and `append_receipt`'s
    /// own check. So the helper worked exactly until a second agent committed
    /// anything, and the first thing that happens on a new node is another agent (the
    /// faucet) committing.
    ///
    /// THE CANARY: put `s.cclerk.receipt_chain().last().map(|r| r.receipt_hash())`
    /// back in `commit_effects_as` and this goes red on `rejected: receipt chain
    /// mismatch: expected None, got Some(..)`.
    ///
    /// ADJACENT GAP, deliberately not exercised here: `commit_effects_as` cannot act
    /// on a cell the FAUCET funded, for an unrelated reason. The faucet leaves a
    /// zero-pk landing stub, and this helper — unlike `api.rs::post_submit_turn` —
    /// never calls `signed_turn_validation::claim_signer_actor_cell`, so the executor
    /// verifies the action against the stub's pk and refuses with `hybrid: Ed25519
    /// (classical) signature half failed`. Driving the stranger receipt in directly
    /// keeps this test on the defect it is about.
    #[tokio::test]
    async fn commit_effects_as_commits_when_the_wide_log_head_is_a_stranger() {
        let dir = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(dir.path(), vec![]).expect("node state");
        let mut s = state.write().await;
        s.unlocked = true;

        // The operator's own agent cell on the ledger, funded to pay the metered fee.
        let operator = local_agent_cell(&s);
        let operator_pk = s.cclerk.public_key().0;
        let cell = dregg_cell::Cell::with_balance(operator_pk, default_token_id(), 0);
        assert_eq!(cell.id(), operator, "agent-cell derivation must match");
        s.ledger.insert_cell(cell).expect("insert operator cell");
        assert!(
            s.ledger
                .get_mut(&operator)
                .expect("operator cell")
                .state
                .credit_balance(1_000_000),
            "operator accepts funding"
        );

        crate::faucet_grant_e2e::append_stranger_receipt(&mut s, dregg_cell::CellId([0xEE; 32]));
        assert_eq!(
            s.cclerk.agent_receipt_head_hash(&operator),
            None,
            "precondition: the operator is at genesis while the wide head is not"
        );

        let receipt_hash = commit_effects_as(
            &mut s,
            operator,
            "receipt_head_probe",
            vec![dregg_turn::action::Effect::SetField {
                cell: operator,
                index: 3,
                value: [0xcd; 32],
            }],
        )
        .unwrap_or_else(|e| panic!("commit_effects_as refused the operator's own turn: {e}"));

        assert_eq!(
            s.cclerk.agent_receipt_head_hash(&operator),
            Some(receipt_hash),
            "the operator's causal head must now be the receipt this call produced"
        );
        assert_eq!(
            s.ledger
                .get(&operator)
                .and_then(|c| c.state.get_field(3).copied()),
            Some([0xcd; 32]),
            "the effect must be on the authoritative ledger, not merely accepted"
        );
    }
}
