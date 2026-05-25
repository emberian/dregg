# multi-node-devnet

Multi-node, multi-federation devnet orchestration for real Silver-Vision
end-to-end testing. Boots two federations (F1, F2) of three nodes each,
cross-registers their committee descriptors, and exposes a set of
named scenario scripts that exercise cross-federation flows over the
running substrate.

## Layout

```
demo/multi-node-devnet/
├── README.md                       (this file)
├── start_devnet.sh                 boot both federations (6 nodes)
├── stop_devnet.sh                  graceful TERM, then KILL after 5s
├── reset_devnet.sh                 stop + wipe state/ entirely
├── run_all_scenarios.sh            convenience: run every scenarios/*.sh
├── lib/
│   └── common.sh                   topology, ports, data-dirs, helpers
├── scenarios/
│   ├── cross_fed_handoff.sh
│   ├── federation_attestation.sh
│   ├── bilateral_transfer.sh
│   ├── intent_match_cross_fed.sh
│   └── peer_exchange_bypass.sh
├── expected/
│   ├── cross_fed_handoff.json
│   ├── federation_attestation.json
│   ├── bilateral_transfer.json
│   ├── intent_match_cross_fed.json
│   └── peer_exchange_bypass.json
└── state/                          created on boot; wiped by reset
    ├── F1/genesis/                 federation-wide genesis output
    ├── F1/node-{1..3}/             per-node data-dir
    ├── F2/genesis/
    ├── F2/node-{1..3}/
    ├── pids/                       one PID file per running node
    ├── logs/                       per-node tracing + per-scenario results
    └── .devnet-up                  sentinel: present iff devnet booted
```

## Topology

| Federation | Node    | HTTP API (loopback) | Gossip port | Data dir                                |
|------------|---------|---------------------|-------------|-----------------------------------------|
| F1         | node-1  | `127.0.0.1:7811`    | 7911        | `state/F1/node-1`                       |
| F1         | node-2  | `127.0.0.1:7812`    | 7912        | `state/F1/node-2`                       |
| F1         | node-3  | `127.0.0.1:7813`    | 7913        | `state/F1/node-3`                       |
| F2         | node-1  | `127.0.0.1:7821`    | 7921        | `state/F2/node-1`                       |
| F2         | node-2  | `127.0.0.1:7822`    | 7922        | `state/F2/node-2`                       |
| F2         | node-3  | `127.0.0.1:7823`    | 7923        | `state/F2/node-3`                       |

Each federation's `federation_id` is derived from
`BLAKE3("pyana-fed-id-v1" || sorted_committee_pubkeys || epoch=0)` via
`pyana_federation::derive_federation_id_with_epoch` — see
`node/src/genesis.rs:133` and audit finding F1 in
`AUDIT-federation.md`. Because the committee keys are freshly
generated on every `reset_devnet.sh`, the next boot produces *new*
`federation_id`s. Per the greenfield posture (improve don't degrade)
there is no on-disk shape to preserve across resets.

Within each federation, nodes gossip-peer the other two (federation_peers
= comma-separated `127.0.0.1:gossip_port` of siblings). Across
federations, peering is bilateral by file copy at startup: each
federation's genesis descriptor is registered with every node in the
peer federation via `pyana-node register-federation`.

## Prerequisites

The orchestration shell scripts depend on the `pyana-node` binary being
built and findable at `$REPO_ROOT/target/debug/pyana-node` (overridable
via the `NODE_BIN` environment variable). **This lane does not invoke
`cargo`.** Build the binary out-of-band:

```sh
# from repo root, in a separate shell:
cargo build -p pyana-node -p pyana-verifier
```

Or rely on the build step inside `demo/two-ai-handoff/run.sh`, which
produces the same binary.

The scenarios also use:
- `bash` 4+
- `jq` (every scenario reads/writes JSON; mandatory)
- `curl`
- `python3` (used for cryptographic hash derivations and nonce
  generation; no third-party packages)

## Boot

```sh
cd demo/multi-node-devnet
./start_devnet.sh
```

Expected output (federation_ids will differ on each fresh boot):

```
[devnet] step 1 — generate genesis for each federation
         ok F1 genesis ok (federation_id=a3f1b7c8…)
         ok F2 genesis ok (federation_id=9c2e51a0…)
[devnet] step 2 — initialize per-node data directories
         F1 node-1  data-dir=…/state/F1/node-1  http=7811  gossip=7911
         …
[devnet] step 3 — cross-register peer federation descriptors (bilateral trust root)
         F1 node-1 ← registered F2
         F2 node-1 ← registered F1
         …
         ok all nodes know both federations
[devnet] step 4 — launch all 6 nodes
         F1 node-1 pid=… http=7811 gossip=7911
         …
[devnet] step 5 — wait for HTTP readiness
         ok F1 node-1 listening on :7811
         …
[devnet] step 6 — devnet topology summary
         F1 federation_id = a3f1b7c8…
           F1-node-1  http=http://127.0.0.1:7811  pid=…
…
[devnet] devnet UP — see state/logs/ for per-node tracing
```

## Run scenarios

```sh
# individually:
./scenarios/cross_fed_handoff.sh
./scenarios/federation_attestation.sh
./scenarios/bilateral_transfer.sh
./scenarios/intent_match_cross_fed.sh
./scenarios/peer_exchange_bypass.sh

# or all of them:
./run_all_scenarios.sh
```

Each scenario writes a result JSON to
`state/logs/scenarios/<name>/result.json` and compares it against
`expected/<name>.json` (the `must_pass` and `must_not_pass` lists). Exit
code 0 iff every assertion in `must_pass` was recorded `true` and every
assertion in `must_not_pass` was correctly detected (also recorded
`true` — see the `must_not_pass_explanation` block in each
`expected/*.json` for the semantics).

### Scenarios — what each demonstrates

#### `cross_fed_handoff.sh`

Alice on F1 creates a bearer cap targeting `bob_cell` on F2. The URI
traverses an out-of-band channel (file copy from
`state/logs/scenarios/cross_fed_handoff/alice-urigen/` to `bob-inbox/`).
The scenario asserts that both federations expose `/federation/roots`,
the cert's `target_federation` field is bound to F2, and tampered/replay
artifacts are structurally distinguishable.

Mirrors `SILVER-VISION-E2E-VERIFICATION.md` §1 step 1–3.

#### `federation_attestation.sh`

F1 produces an AttestedRoot signed by its committee; F2 does the same.
Each federation's descriptor is on disk in every peer-federation node's
`known_federations/<other_fed_id>.json`. A tampered descriptor (extra
validator appended, declared federation_id unchanged) is rejected by
`pyana-node register-federation` because the recomputed
H(sorted_pubkeys || epoch) mismatches the declared id (audit F1).

Mirrors `SILVER-VISION-E2E-VERIFICATION.md` §4.

#### `bilateral_transfer.sh`

γ.2 bilateral binding: `transfer_id =
BLAKE2b("pyana-gamma2-transfer-id-v1" || alice_cell || bob_cell ||
amount || nonce || federation_id_F2)`. The scenario asserts the id is
deterministic, distinguishes target federation (same inputs bound to F1
yield a different id), the credit/debit direction bits XOR to 1, and an
amount mismatch in the pair is detectable.

Mirrors `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`. The off-AIR pair verifier
is the next milestone.

#### `intent_match_cross_fed.sh`

Trustless intent submission to F1 (route `/intents/trustless`) with
`target_federation = F2`. F1's committee decrypts; the action settles
on an F2 cell. The scenario asserts route presence, threshold
sanity (`quorum_threshold(3) = 3`, which is `(2/3)+1`), and the routing
fields are correctly cross-federation. An adversarial intent that
collapses `submitter_federation := target_federation` is detected.

Mirrors `STARBRIDGE-APPS-PLAN.md` intent-app §.

#### `peer_exchange_bypass.sh`

Two sovereign cells (one on F1, one on F2) exchange directly via
`/turns/peer-exchange`. Each emits a `SovereignCellWitness` (Ed25519 +
sequence) over its own transition; neither federation executes the
remote effect. The `peer_exchange_id` is committee-invariant (function
of cells only). Sovereign witnesses self-verify against the cell's own
key without referencing either federation's committee.

Mirrors `FEDERATION-AS-CELL.md` + `STORAGE-AS-CELL-PROGRAMS.md`.

## Shutdown / reset

```sh
./stop_devnet.sh    # graceful: SIGTERM, then SIGKILL after 5s
./reset_devnet.sh   # stop + rm -rf state/  (regenerates fresh genesis next boot)
```

## Troubleshooting

### "node binary not found at …/target/debug/pyana-node"

Build it out-of-band. From the repo root:

```sh
cargo build -p pyana-node -p pyana-verifier
```

Or set `NODE_BIN=/abs/path/to/your/pyana-node` before invoking
`start_devnet.sh`.

### "FX node-Y never came up on :NNNN"

Look at `state/logs/F<X>-node-<Y>.log`. Common causes:

- **Port already in use.** Another devnet (or a stray
  `pyana-node run` from a previous session) holds the port. Run
  `./stop_devnet.sh && lsof -i :7811-7823,7911-7923` to find the
  squatter.
- **genesis.json not loadable.** Check the log for "failed to parse
  genesis.json"; usually a stale `state/` from a partial reset.
  `./reset_devnet.sh` cleans it.
- **Missing `node.key`.** The boot script copies
  `state/F<X>/genesis/node-<I-1>.key` (0-based) to
  `state/F<X>/node-<I>/node.key` (1-based). If the `genesis` subcommand
  emitted a different layout, the copy step warns. Inspect
  `state/F<X>/genesis/` directly.

### "register-federation failed"

`state/logs/F<X>-node-<Y>-register-F<Z>.log` will name the cause. The
most common are:
- Peer's `genesis.json` not present (didn't run step 1 cleanly).
- Tampered descriptor: the federation_id declared inside the
  descriptor doesn't equal `H(sorted_pubkeys || epoch)`. The CLI is
  intentionally strict here (audit F1).

### Scenarios pass on a fresh boot but fail on re-run

The `must_not_pass` cases (replay, tamper) construct *new* artifacts
relative to the previous run; some scenarios are stateful (`bob-inbox`
persists across runs). To re-run from a clean slate, prefer
`./reset_devnet.sh && ./start_devnet.sh && ./run_all_scenarios.sh`.

### "cargo build failed" — not applicable

This lane never invokes cargo. If a scenario log references cargo,
that's a script bug; file an issue.

## Why no docker-compose.yml?

The repository's policy (per
`feedback-avoid-npm-direct.md`) is that Docker is for *isolation*, not
for *build*. Containerising the devnet at runtime is reasonable when
the goal is supply-chain isolation, but for the multi-node devnet the
processes are vanilla `pyana-node run` invocations on loopback —
adding a docker-compose stack would only buy:

- Process isolation (each node in its own container)
- Hostname routing (`F1-node-1`, etc.)

…neither of which is load-bearing for the substrate verification this
lane targets, both of which add CI fragility for new contributors
(must have Docker; image-build path; volume mounts for `state/`).

When `docker-compose` *does* become valuable — e.g. when a scenario
needs to drive a *byzantine* federation in isolated network namespaces
— a `docker/` subdirectory is the right place. That work is explicitly
deferred to Phase 2 (out of scope for this lane).

If a future contributor wants the docker variant, the right shape is:
each federation gets a network namespace; gossip ports use container
hostnames (`F1-node-1:9420`) so the federation_peers CLI flag is
docker-friendly; volume-mount `state/<fed>/<node>` per container; one
service per node. Six services total. The image stage builds
`pyana-node` once and copies the binary into every service.

## Scope discipline

This lane (per the spec) touches only `demo/multi-node-devnet/`. It
does NOT modify `node/`, `federation/`, `blocklace/`, `wire/`,
`captp/`, `sdk/`, `cell/`, `turn/`, `circuit/`, `app-framework/`,
`apps/`, `starbridge-apps/`, `intent/`, `dfa/`, or `bridge/`.

When a scenario's `must_pass` list grows after a lane lands (lane A /
D / F-redux / γ.2 — see `SILVER-VISION-E2E-VERIFICATION.md` §2), the
shape is: edit the relevant `scenarios/<name>.sh` to drive the new
substrate, edit `expected/<name>.json` to widen `must_pass` /
`must_not_pass`. Do NOT remove or comment out an assertion to make
the scenario "pass"; that is the degrade-not-improve antipattern.

## Greenfield posture

There is no production deployment to protect; no archive of receipts to
preserve; no API surface that must remain backwards compatible. If a
scenario's `expected.json` grows when a lane lands, the scenario IS the
spec for that lane's user-visible surface. The expected.json files
already name their `blocked_on` lanes explicitly so the substrate
maturity is auditable from one place.

## Out of scope (explicit)

- Production-grade orchestration (k8s, systemd, supervisor)
- Adversarial *byzantine* federations (one federation acting against
  another) — Phase 2 lane
- Persistent state across reboots — devnet resets cleanly by design
- TLS / WAN deployment — loopback only
- Multi-host topology — single-machine only
- Cipherclerk / app-framework demos — see `demo/two-ai-handoff/` and
  `demo/silver-vision-e2e/`

## Pointers

- `SILVER-VISION-E2E-VERIFICATION.md` — the canonical design this lane
  serves
- `STARBRIDGE-APPS-PLAN.md` — apps that will run on top of this devnet
- `demo/two-ai-handoff/` — single-federation companion demo (working
  baseline)
- `demo/silver-vision-e2e/expected.json` — the *substrate* spec; this
  lane's `expected/*.json` files are scenario-shaped subsets
- `node/src/main.rs::register-federation` — the cross-fed trust-root CLI
- `node/src/genesis.rs::run_genesis` — committee key generation +
  federation_id derivation
