# The node & server-host

`dregg-node` is the federation node daemon: it hosts an agent cipherclerk, participates in
consensus, and serves a localhost HTTP/WS API for submitting turns and reading committed
state. Its package description: "Federation node daemon — hosts an agent cipherclerk,
participates in consensus, and serves a localhost API" (`node/Cargo.toml:10`).

This doc covers the node's request surface — the router, the turn-submission ingress paths,
the receipt SSE stream — and the **deos-host**, the userspace deos-js "private server" the
node can host inside its own process.

## Subcommands

`node/src/main.rs` is a 15-line entry shim: it parses the CLI and hands off to
`dregg_node::run` (`node/src/main.rs:1`–`:15`). Everything else — the `clap` `Command` enum,
boot, the HTTP API, consensus — lives in the `dregg_node` library. The commands
(`node/src/lib.rs:104`):

- **`run`** — the daemon: HTTP API + federation sync (`node/src/lib.rs:106`). Flags include
  `--port`/`--bind` (`:108`, `:113`), `--federation-peers`, `--data-dir`/`--key-file`,
  `--gossip-port`, `--federation-mode` (`solo`|`full`, default `solo`, `:235`), `--consensus`
  (`blocklace`, the only engine, `:240`), `--prove-turns` (prove + verify-gate every finalized
  turn, also `DREGG_PROVE_TURNS=1`, `:160`), `--enable-faucet`, `--enable-pruning`, the
  block-cadence / idle-heartbeat / min-block-interval timers (`:189`–`:220`), the blocklace
  checkpoint/wave tuning (`:174`, `:178`), `--groups`, `--auto-approve-joins`,
  `--cors-origin`, and `--deos-program` (`:285`).
  The async prover that attests API-committed turns (`node/src/prove_pool.rs`) reads three
  environment knobs: `DREGG_PROVE_WORKERS` (concurrent proofs, default 2; `0` turns async
  proving off and leaves receipts committed-but-unattested), `DREGG_PROVE_THREADS` (rayon
  threads per proof in a dedicated `dregg-prove-N` pool; unset = the global pool, one thread
  per logical CPU) and `DREGG_PROVE_QUEUE_DEPTH` (default 256).
- **`init`** — create the data dir and generate a node keypair, writing `node.key` at mode
  `0600` and printing the public key (`node/src/lib.rs:289`, `:1793`).
- **`status`** — raw TCP liveness probe of the HTTP port (no HTTP client dep;
  `node/src/lib.rs:296`, `:1845`).
- **`mud-client`** — boot a self-contained playable MUD and drop into a REPL (requires the
  `deos-host` feature; `node/src/lib.rs:307`). See "Playable engines" below.
- **`mcp`** — run as a Model Context Protocol server over stdio for AI assistants. Tracing
  goes to stderr so stdout stays clean JSON-RPC (`node/src/lib.rs:574`–`:577`); the
  cipherclerk starts unlocked since stdio is a single-user CLI (`node/src/lib.rs:317`,
  `:1881`).
- **`register-federation`** — register a peer federation's descriptor into
  `<data-dir>/known_federations/<id>.json` after recomputing and matching its `federation_id`
  (rejects a tampered descriptor, audit F1; `node/src/lib.rs:338`, `:2275`).
- **`genesis`** — generate devnet genesis (keys, `genesis.json`, env files;
  `node/src/lib.rs:351`).
- **`relay`** — run as a hosted CapTP inbox relay operator (`node/src/lib.rs:374`).
- **Federation-operator commands** — the validator onboarding + live-reconfiguration set:
  **`gen-validator-key`** (idempotent keygen, prints the pubkey to hand to the operator,
  `node/src/lib.rs:431`); **`join`** (peer to a bootstrap node, sync the blocklace, follow —
  or vote, if this key is in the committee; requires a committee `genesis.json`, and a
  non-member auto-proposes membership, `:450`); **`add-validator`** (the offline authority
  op: fold pubkeys into `genesis.json`'s committee, re-derive `federation_id` + BFT
  threshold — filesystem access to the data dir IS the authority, `:489`);
  **`propose-epoch-transition`** (LIVE validator-set change on a running node — applies only
  once a quorum of the current committee ratifies through finality, no genesis re-roll,
  `:512`); and **`approve-membership`** (the admit half: each committee operator approves a
  pending proposal until quorum, `:541`).

`run(cli)` (`node/src/lib.rs:561`) installs the rustls ring provider (`:562`), arms the
verified-Lean distributed coordination gates (`dregg_exec_lean::register_distributed_gates`,
`:572`), and initializes tracing before dispatch (`:574`).

### Boot sequence (`run`)

`run_node` (`node/src/lib.rs:802`): expand `--data-dir` (exits if absent — run `init` first,
`:829`); warn on a `.devnet` marker (`:840`); fail CLOSED if the binary was linked without
the verified Lean executor archive — a marshal-only build must never deploy silently as the
verified node (`:845`); build `NodeState` (`:1063`); spawn the async `ProvePool` and attach
it (`:1075`); load `genesis.json` if present (committee epoch, validator keys, threshold,
checkpoint interval, `genesis_moves` issuer-seeding via `materialize_genesis_cells`, and
starbridge factory cells, `:1079`–`:1231`); backfill default starbridge cells when
`--enable-faucet` and no genesis seeded them (`:1241`); derive the boot committee from the
persisted chain (`:1356`); load `known_federations/` (`:1437`); configure pruning + full-turn
proving + solo consensus; install the Prometheus recorder (`:1590`); start blocklace sync
(`:1657`); assemble the CORS allowlist (`:1682`); build the router and serve it with graceful
shutdown.

## Boot & serving

The `Run` subcommand starts the daemon. It binds `127.0.0.1` by default; `--bind 0.0.0.0`
exposes it to the network and logs a warning that the faucet / cipherclerk / bridge endpoints
become reachable (`node/src/lib.rs:1714`–`:1721`). The HTTP API listens on `--port` (default
`8420`, `node/src/lib.rs:108`).

`run_node` builds the router via `api::router_with_cors(...)`, wraps it
`.into_make_service_with_connect_info::<SocketAddr>()` (so handlers see the peer IP), binds a
`tokio::net::TcpListener`, and runs `axum::serve(listener, app).with_graceful_shutdown(...)`
(`node/src/lib.rs:1701`–`:1707`, `:1725`, `:1781`–`:1784`). On shutdown it persists state
(`node/src/lib.rs:1787`).

## The router

`router_with_cors(state, enable_faucet, metrics_handle, cors_origins)` assembles three route
groups (`node/src/api.rs:1627`):

- **public_routes** — no auth (`node/src/api.rs:1643`): `/status`, `/health`,
  `/api/node/producer`, `/api/cells`, `/api/cell/{id}`, `/api/receipts`,
  `/api/server/{cell}/affordances` (deos-host discovery), `/api/turn/{hash}/proof`,
  `/api/events`, `/api/events/stream` (the SSE receipt stream, `node/src/api.rs:1715`),
  `/checkpoint/*`, `/pir/*`, and more.

  ⚑ `/api/turn/{hash}/proof` **always carries `proof_status`**, and its absence
  cases are three, not one (changed 2026-08-05): `200`/`proved` with the bytes,
  `410 Gone`/`generation_failed` + `error` when the finalized proof did NOT
  verify (recorded under `full_turn_proof_failed:{hash}`, never coming — stop
  polling), and `404`/`absent` when nothing is recorded either way (proving
  disabled, or no proof applies). It previously answered a bare `404` for all
  three, so a poller could not tell a failed proof from a pending one.

  ⚑ **`/api/turn/{hash}/anchor` — the committee-signed per-turn anchor (NEW 2026-08-06).**
  A proof artifact is only worth re-verifying against something *external*. This route
  serves that something. `anchor_hex` is the postcard encoding of
  `dregg_federation::TurnAnchorV1`; a holder decodes it and calls
  `.verify(&committee)` with a roster **they** trust (from genesis, not from this node),
  which recomputes `TurnReceipt::receipt_hash()`, re-roots it through
  `merkle_root_of_receipt_hashes` into the attestation's `receipt_stream_root`, and
  requires `>= threshold` distinct committee signatures over
  `AttestedRoot::signing_message()`. The verified `turn_hash` is then the
  `expected_turn_hash` argument to `dregg_sdk::verify_full_turn_bound`.

  * `200` / `anchor_status: "anchored"` — `anchor_hex`, `anchor_len`,
    `artifact_format: "DTA1"`, plus a **non-authoritative** summary (`height`,
    `block_id`, `receipt_hash`, `ledger_root`, `receipt_stream_root`, `threshold`,
    `receipt_covering_signatures`, `chain_position_signatures`). Verify `anchor_hex`;
    never the summary.
  * `404` / `anchor_status: "not_committed"` — no committed turn under this hash.
  * `409` / `anchor_status: "no_attestation"` — the turn committed but nothing at its
    height binds a receipt stream, so no signature reaches it. A conflict, not an
    absence.
  * `400` — the hash is not 64 hex characters.

  ⚠ **The anchor carries an 8-felt state-commit pair that is NOT the proof's.** The
  receipt's `pre_state_hash`/`post_state_hash` are the chip 8-felt consensus commitment
  under `state_commit::consensus_ctx` (whole-ledger `cells_root`, `iroot =
  empty_iroot()`); the full-turn proof publishes the rotated leg's commitment under a
  single-cell context ledger with the real receipt-chain `iroot`. They differ —
  measured, with both causes isolated, in
  `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`. Passing the
  receipt's pair to `verify_full_turn_bound` as `expected_old_commit` refuses every
  honest proof, so this endpoint does **not** advertise them as such and the two
  endpoint `CommitmentMismatch` teeth remain reflexive. That is undone work (align the
  executor's and the prover's `V9RotationContext`), priced in
  `docs/DESIGN-pi-authority.md`.

  ⚑ **How much committee is actually behind it — CLOSED 2026-08-07 (schema epoch 24).**
  `AttestedRoot::quorum_signatures` receives exactly ONE push on the live path, the local
  node's, because `PeerMessage::AttestedRootUpdate` has zero handlers. Until this change
  that was the only preimage covering `receipt_stream_root`, so the anchor verified on a
  threshold-1 federation and **refused on a larger committee**: the `>= threshold` hybrid
  vote quorum signed `dregg-finalization-vote-v3 || block_id || merkle_root` and reached
  no receipt.

  The finalization-vote preimage is now
  `dregg-finalization-vote-v4 || block_id || merkle_root || framed(receipt_stream_root)`,
  so the quorum a real committee assembles DOES reach the receipt. `TurnAnchorV1::verify`
  counts the UNION of distinct committee members across both legs — `quorum_signatures`
  over `AttestedRoot::signing_message()` and `hybrid_quorum` over
  `AttestedRoot::hybrid_quorum_message()` — and both preimages bind the same
  `(block_id, merkle_root, receipt_stream_root)` of the same root. `position_quorum_met`
  still reports which leg carried it, because "the committee's cross-node quorum" and
  "this node's own attestation" are different facts and a holder should see which one it
  got. A federation whose vote quorum has not yet converged still refuses, by name.
  Exhibited end to end in
  `node/tests/committee_signature_covers_a_per_turn_value.rs`.
- **protected_routes** — gated by the `require_auth` middleware layer
  (`node/src/api.rs:1780`, layered at `:1884`): `/turn/submit`, `/turns/submit`,
  `/turns/submit-encrypted`, `/turns/aggregate`, `/ws`, `/cipherclerk/*`, `/intents*`,
  `/cells/*`, `/turn/atomic/*`, conditional-turn routes, and the merged ORGANS service
  routers (storage gateway, trustlines, channels, equivocation court, DKG —
  `node/src/api.rs:1865`–`:1882`).
- **path_aliases** — `/api/node/*` and `/api/turns/*` prefixed duplicates for bot/app
  compatibility (`node/src/api.rs:1894`).

Two rate limiters are constructed: passphrase/unlock (5 attempts / 60s,
`node/src/api.rs:1637`) and turn submission (`DEFAULT_TURN_RATE_LIMIT` = 60 / 60s per IP,
`node/src/api.rs:1320`, `:1640`). The turn limiter is cloned into each submit closure.

### Auth

`require_auth` (`node/src/api.rs:1397`) runs as a `middleware::from_fn_with_state` layer over
the protected routes. Before any passphrase is set, it restricts access to loopback (resolving
the real client IP through `X-Forwarded-For` only when `DREGG_TRUSTED_PROXIES` names the
direct peer, `node/src/api.rs:1408`–`:1430`). Once a `bearer_seed` exists, it requires
`Authorization: Bearer <token>` where the token is `blake3::derive_key("dregg-api-bearer-v1",
bearer_seed)` (`node/src/api.rs:1450`).

## Node state

`NodeState` is a `Clone` handle wrapping `Arc<RwLock<NodeStateInner>>` plus an `events_tx`
broadcast channel, a gossip handle, and the async prove pool (`node/src/state.rs:135`).
`read()`/`write()` return the tokio `RwLock` guards (`node/src/state.rs:1205`, `:1210`).

`NodeStateInner` (`node/src/state.rs:152`) holds the live system: `cclerk:
AgentCipherclerk` (identity, wallet, the receipt chain), `ledger: Ledger`, `store:
PersistentStore`, `unlocked: bool`, the intent pool, the consensus queue, pending
conditionals, federation registry, the SSE `event_log: VecDeque<CommittedEvent>`
(`node/src/state.rs:420`), `lean_producer_enabled` (`:307`), `full_turn_proving_enabled`
(`:293`), `solo_consensus` (`:465`), and `deos_server_surfaces` — the discoverable deos-host
affordance surfaces (`:471`).

`NodeEvent` (`node/src/state.rs:116`) is the broadcast payload: `Root`, `Revocation`,
`Receipt { hash }`, `InvalidBlocklaceBundle`, `Intent`. `subscribe_events()` hands out a
receiver; `emit(event)` fans out (errors ignored — no subscribers is fine,
`node/src/state.rs:1561`, `:1566`).

## Turn submission ingress

There are three distinct submit handlers, all rate-limited per real client IP and all
requiring `s.unlocked`.

### `/turns/submit` — signed-envelope ingress (the remote-agent path)

`post_submit_signed_turn` (`node/src/api.rs:3414`) is the canonical path for a remote agent's
turn. The body is a postcard-encoded `dregg_sdk::SignedTurn` (`node/src/api.rs:3429`). It:

1. Verifies `signed.signer.verify(turn_hash, signature)` and rejects with `accepted:false` on
   failure (`node/src/api.rs:3435`). When the envelope carries a post-quantum half, the
   ML-DSA signature is verified over the SAME turn hash, fail-closed: a present-but-invalid
   PQ half rejects regardless of the staged `require_pq` flag (`node/src/api.rs:3449`–`:3468`).
2. Derives the expected agent `CellId::derive_raw(signer, blake3("default"))` and rejects if
   `signed.turn.agent` does not match it (`node/src/api.rs:3470`).
3. When the turn's agent is the node operator's own default cell (`is_operator_agent`,
   derived via `executor_setup::local_agent_cell`, `node/src/api.rs:3502`), checks the
   optional `previous_receipt_hash` against the cipherclerk chain head
   (`node/src/api.rs:3509`–`:3524`). A foreign client's turn is decoupled: its receipt
   chain is its own and is NOT gated against the node's cclerk head — gating it would
   serialize every client through one node-owned chain (`node/src/api.rs:3496`–`:3508`).
4. Arms an O(touched) undo journal on the ledger (a restore point, not a full pre-state
   clone, `node/src/api.rs:3526`), builds a submit executor, and executes through the **one
   producer gate**: `executor_setup::execute_via_producer(executor, &signed.turn,
   &mut s.ledger, lean_producer_enabled)` (`node/src/api.rs:3582`). The touched-cell
   pre-ledger for witness building comes from `pre_turn_touched_ledger()`
   (`node/src/api.rs:3591`).
5. On `TurnResult::Committed`, appends the receipt to the cipherclerk chain (rolling the
   ledger back to the restore point if the append fails, `node/src/api.rs:3637`), prepares an
   asynchronous rotatable attestation (`prepare_rotatable_turn`, `node/src/api.rs:3657`,
   defined at `:2872`), pushes a committed event (`:3686`), drops the write lock (`:3697`),
   then **off the lock** enqueues async proving (`:3701`), emits `NodeEvent::Receipt`
   (`:3711`), gossips the turn (`:3716`), and submits the `TurnArtifactBundle` to the
   blocklace (`node/src/api.rs:3723`–`:3736`).

The response is `SubmitSignedTurnResponse { accepted, turn_hash, signer, action_count,
proof_status, has_witness, witness_count, error }` (`node/src/api.rs:445`).

### The one producer gate

`execute_via_producer` (`node/src/executor_setup.rs:120`) is the single entry every committed
turn passes through. When `lean_producer_enabled` is false it is exactly
`executor.execute(turn, ledger)` (the legacy Rust producer). When enabled it calls
`dregg_exec_lean::produce_via_lean`, making the verified Lean executor authoritative for the
covered turn-set: a Lean↔Rust disagreement on a covered turn is logged as a Rust bug (the
verified verdict was committed, not overridden, `node/src/executor_setup.rs:150`–`:168`); a
turn outside the covered set is explicitly fenced onto the legacy Rust path
(`node/src/executor_setup.rs:169`–`:180`). The submit executor itself
(`new_submit_executor`) is a `TurnExecutor` with the `LeanShadowObserver` injected and block
height set to `Next` (`node/src/executor_setup.rs:262`).

### Proof status

Proving runs **off the commit path** (F-DOS-1). After commit the handler builds the rotatable
turn and reports `ActivityProofStatus::ProofPending` if witness material was produced,
`NotRequired` otherwise. `enqueue_async_proof` hands a `ProveJob` to the prove pool and marks
the receipt proof-pending; if no pool is installed the committed receipt is left unattested
(the executor already validated + committed it, so the commit is sound,
`node/src/api.rs:2934`–`:2963`). `ActivityProofStatus` variants: `Proved`, `ProofPending`,
`NotRequired`, `MissingPreState`, `ProofGenerationFailed`, `NotCommitted`
(`node/src/state.rs:622`).

### `/turn/submit` — the operator's thin local path

`post_submit_turn` (`node/src/api.rs:3053`) takes a JSON `SubmitTurnRequest` of action specs.
It **ignores the body's `agent`** and derives the agent from the node's own cipherclerk pubkey
(`CellId::derive_raw(s.cclerk.public_key(), blake3("default"))`) — closing a confused-deputy
attack where a caller targeted a victim cell's c-list with the operator's signature
(`node/src/api.rs:3074`–`:3082`). Each action is signed by the operator's cipherclerk over the
executor's verifying federation id (`federation_id_for_executor`, which on a solo node is
`blake3(pubkey)`, `node/src/api.rs:3102`). Response: `SubmitTurnResponse`
(`node/src/api.rs:435`).

### `/turns/submit-encrypted` — encrypted-turn ingress

`post_submit_encrypted_turn` (`node/src/api.rs:3990`) takes a raw postcard
`dregg_turn::EncryptedTurn` (octet-stream, not JSON). The executor's X25519 unsealer secret is
derived from the cipherclerk (`derive_symmetric_key("dregg-turn-unsealer-v1")`,
`node/src/api.rs:3955`); the matching public key is served at `GET /turns/encryption-key` so a
sender can encrypt to the executor (`node/src/api.rs:3961`, route at `:1836`). Only the
receipt's `was_encrypted: true` bit is disclosed after commit (`node/src/api.rs:3988`).

### `/turns/aggregate` — cross-node bilateral aggregate

`post_aggregate_bundle` (`node/src/api.rs:3838`) accepts a canonical `SignedTurn` plus ≥2
independently-sourced per-cell `WitnessedReceipt` artifacts, runs `prove_aggregated_bundle`
to produce a real outer STARK proof (`node/src/api.rs:3922`), then `verify_aggregated_bundle`
before returning. Per-WR soundness gates (`require_scope2_witness`, `verify_bilateral_chain`)
run inside the aggregator (`node/src/api.rs:3832`–`:3837`).

## The receipt SSE stream — `GET /api/events/stream`

`events_stream` (`node/src/events.rs:141`) is the node's "nervous system" edge: a
Server-Sent-Events broadcast of every receipt the node commits. The **broadcast is only a
wake-up**; the cipherclerk receipt chain is the cursor's source of truth, so a lagged
broadcast subscriber loses nothing — the cursor re-reads the chain and catches up
(`node/src/events.rs:10`–`:16`).

Mechanics:
- Subscribe to the broadcast **before** reading the chain head, so anything committed between
  the snapshot and the first `recv()` still wakes the cursor (`node/src/events.rs:146`).
- A reconnecting client sends `Last-Event-ID: <chain_index>`; the stream resumes from the next
  chain entry (a fresh connection tails from the current head, `node/src/events.rs:150`–`:159`).
  Delivery is exactly-once per connection, at-least-once across reconnects
  (`node/src/events.rs:14`).
- The `unfold` loop drains the chain from `next` to the chain length, emitting each
  `ReceiptEvent` as an SSE `event("receipt")` with `id` = chain index; when drained it sleeps
  on the broadcast until the next commit (`node/src/events.rs:167`–`:207`).
- Filters: `?cell=<hex id>` (agent cell or any cell named by the receipt's emitted events /
  commit record) and `?kind=<effect kind>` (matched against effect summaries),
  `node/src/events.rs:17`–`:20`, `:35`.
- A 30s keep-alive comment keeps proxies from closing the stream (`node/src/events.rs:210`).

`ReceiptEvent` (`node/src/events.rs:46`) carries `chain_index`, `receipt_hash`, `turn_hash`,
touched `cells`, effect `kinds`, `height`, `has_proof` (true if a witnessed receipt or
persisted full-turn proof exists **at send time** — proofs land asynchronously,
`node/src/events.rs:61`, `:96`), `finality`, `timestamp`, and the full canonical
`dregg_turn::TurnReceipt`.

A separate WebSocket handler (`/ws`, `node/src/ws.rs`) pushes the same `NodeEvent` topics and
accepts commands (subscribe, authorize); message/frame sizes are capped at 1 MiB / 256 KiB
(`node/src/ws.rs:29`–`:31`).

## The deos-host — a userspace private server inside the node

The deos-host (`node/src/deos_host.rs`, opt-in `deos-host` Cargo feature) lets the node host a
headless userspace deos-js "private server": a JS program that holds state in real cells on the
node's ledger and offers cap-gated affordances clients connect to and fire
(`node/src/deos_host.rs:1`–`:6`). The cockpit is then just one client of this; the node is a
headless deos-js-server-host.

### The persistent SpiderMonkey thread

deos-js links SpiderMonkey (`mozjs`); engine init is process-global + one-shot, and the engine
must never be dropped (re-init on a later thread is rejected `AlreadyShutDown`). So the host is
a **single long-lived thread** (`HOST_THREAD: OnceLock<mpsc::Sender<HostJob>>`,
`node/src/deos_host.rs:65`) owning one `JsRuntime` for the process lifetime, running every
hosted program over a job channel (`node/src/deos_host.rs:68`–`:100`). This makes hosting
repeatable: a setup program, then reactive ticks.

### The world sink

`NodeWorldSink` (`node/src/deos_host.rs:131`) implements `deos_js::WorldSink` over the node's
`NodeState`. It runs on the dedicated (non-worker) SpiderMonkey thread, so `block_on` over the
async `RwLock` is sound (`node/src/deos_host.rs:128`–`:130`). Its operations:
- `with_ledger` reads the live ledger (`node/src/deos_host.rs:143`).
- `fire_effects(agent, method, effects)` commits through
  `executor_setup::commit_effects_as` — the same producer-gated commit core the signed-turn
  HTTP ingress runs, minus the wire shell (`node/src/deos_host.rs:148`–`:156`).
- `mint_open_cell(seed, funding)` mints an open-perms funded cell directly onto the ledger —
  the GM superpower of standing up a world vessel, idempotent on an existing id
  (`node/src/deos_host.rs:166`–`:179`).

`commit_effects_as` (`node/src/executor_setup.rs:199`) is the factored core: it builds a `Turn`
under the agent's current nonce + chain head, sizes the fee to `estimate_cost`, executes
through `execute_via_producer`, and appends the committed `TurnReceipt` to the cipherclerk
chain — identical to the HTTP path's committed-turn semantics minus the signature/HTTP/gossip
shell (`node/src/executor_setup.rs:183`–`:198`).

### The boot

`host_server_program(state, seed_label, held, program_js)` (`node/src/deos_host.rs:193`):
1. Mints the server cell (open-perms, funded `1_000_000`, deterministic id from the seed
   label) onto the ledger, idempotent on re-boot.
2. Dispatches a `HostJob` to the persistent thread (`node/src/deos_host.rs:227`), which resets
   the server registry, attaches an `AttachedApplet` as the server agent under `held`
   (`:289`), evals the program (which registers cells + affordances + forks via
   `deos.server.*`), and drains the registry.
3. Publishes the discoverable surface into `NodeState::deos_server_surfaces`: the root surface
   (instance-less affordances) keyed by the server cell, each forked instance keyed by its own
   cell carrying exactly the affordances scoped to it (`node/src/deos_host.rs:254`, `:263`).

`run_node` invokes this on boot if `--deos-program <path>` is given (and the `deos-host`
feature is built — otherwise the flag is inert and warns, `node/src/lib.rs:1741`–`:1778`). The
flag is defined at `node/src/lib.rs:285`.

### Discovery — `GET /api/server/{cell}/affordances`

`get_server_affordances` (`node/src/api.rs:2653`) is public: discovery confers no authority —
the cap tooth is the executor on the fire, not the read (`node/src/api.rs:1657`–`:1659`). An
unknown viewer label refuses fail-closed rather than becoming the broadest viewer
(`node/src/api.rs:2662`). It looks up the cell's published specs, projects them per
`?viewer=<auth label>` through the proven attenuation lattice
(`deos_reflect::AffordanceSurface::project_for`, `node/src/api.rs:2689`), and returns the
visible affordances plus the `executor_federation_id` a client needs to build + sign a fire
turn in one round-trip (`node/src/api.rs:2671`–`:2676`). A client then fires an affordance
through the node's `/turns/submit` ingress as a real verified turn.

## Playable engines: `mud-client` & `shared-world`

Both are `deos-host`-feature-gated engines that boot an **in-process** node, host a deos-js
GM, bind a real TCP listener, and drive the genuine HTTP wire — self-contained demonstrations
of the deos-host architecture.

### `mud_client` — a playable text MUD

`boot_mud_world(player_seed)` (`node/src/mud_client.rs:241`) creates a headless `NodeState`
over a tempdir, marks it `unlocked`, mints a funded open player cell from the seed
(`node/src/mud_client.rs:245`–`:270`), hosts `node/tests/fixtures/mud_play_gm.js` via
`host_server_program` (the GM spawns rooms / character / NPC, grants the player a cap, forks
dungeon instances, registers `move` / `gain-xp` / `descend` affordances,
`node/src/mud_client.rs:272`–`:283`), and binds a real `127.0.0.1:0` listener. The `MudClient`
engine is pure HTTP against any node URL; `run_repl` (`:766`) drives the interactive loop and
`play_interactive` (`:990`) wires it to stdin/stdout — what `dregg-node mud-client` runs.

Each `move` / `gain-xp` / `descend` is a signed turn discovered and fired through
`dregg_sdk_net::{discover_server_affordances, fire_affordance}` and committed on the live
ledger; `look` reads the cells back via `GET /api/cell/{id}`; a `tick` re-hosts the GM's
reactive program (`mud_play_tick.js`) — a GM superpower no player can reach. A forbidden
cross-cell write (e.g. `descend` into the sealed dungeon) is a receipted refusal by the
executor's authority gate (`node/src/mud_client.rs:1`–`:27`).

### `shared_world` — two identities co-inhabiting one world

`boot_shared_world(seed_a, seed_b)` (`node/src/shared_world.rs:173`) is the first rung of
multi-person deos: a headless node hosts `shared_world_gm.js` (a shared board + a presence
seat per identity + a private cell, granting each identity a cap over the shared board and its
own seat); two distinct key-ceremony identities (`SharedClient`) connect over real HTTP and
fire cap-gated turns into the shared board, each turn attributed to its firer (`receipt.agent`,
`node/src/shared_world.rs:1`–`:30`). **Live sync**: each client subscribes to
`/api/events/stream` (`dregg_sdk_net::NodeEvents`), so when A commits, B observes the receipt
and re-reads the changed board. **The over-reach**: B firing `touch-private` over A's private
cell is refused by the executor's authority gate (a receipted refusal leaving the cell
unchanged). This is a demonstrative harness surface consumed by the `shared_world_e2e`
integration proof, not a `--bin` entry point (`node/src/shared_world.rs:31`–`:36`).
