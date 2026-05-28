# Devnet Deployment Preflight - 2026-05-26 (updated 2026-05-28)

Scope: fresh commonquant-ember AWS devnet deploy from the current checkout. No SSH
or deploy was performed.

## Devnet experience fixes (2026-05-28)

Three concrete "deployed devnet feels broken" gaps, all fixed and verified
against a live local node.

1. **Genesis seeds a non-empty ledger.** `dregg-node genesis`
   (`node/src/genesis.rs`) now writes four REAL canonical cells into
   `genesis.json` `initial_cells`: a faucet cell (balance 1,000,000) plus three
   demo agent cells `alice` (50,000), `bob` (25,000), `carol` (10,000). Each
   `id` is the content-addressed `CellId::derive_raw(public_key, token_id)` that
   the executor recomputes in `materialize_genesis_cells`
   (`node/src/main.rs`), so they materialize instead of being rejected. The
   demo agents are backed by real Ed25519 keypairs written as
   `agent-<name>.key` (and `faucet.key`), so they are spendable, not display
   rows. The deployed `deploy/genesis/genesis.json` was regenerated. On a fresh
   `genesis` + `run`, `GET /api/cells` returns 4 cells.

2. **Honest `/status` health.** `healthy` now reflects real consensus liveness
   (blocklace handle attached AND the DAG has produced at least one block),
   NOT the attested-root height. New fields on `/status`:
   - `dag_height` — real blocklace DAG tip (max block `seq`); advances on every
     block including idle heartbeats. This is the honest "chain height N".
   - `block_count` — number of blocks in the local lace.
   - `consensus_live` — whether the consensus task is running.
   - `latest_height` — kept as the attested-root / turn height; only advances on
     turn-bearing finality, so it can legitimately be 0 on a fresh, healthy node
     whose DAG is already tall. Use `dag_height` for "how tall is the chain".

3. **CORS for the deployed devnet (#43).** `dregg-node run` gained a
   `--cors-origin <origin>` flag (repeatable / comma-separated) and reads the
   `DREGG_CORS_ORIGINS` env var (comma-separated); the two are unioned. These
   exact origins are allowed cross-origin IN ADDITION to the always-allowed
   localhost / 127.0.0.1 / [::1] and browser-extension origins. **Default is
   empty (locked down).** Wired through `node/src/main.rs` →
   `api::router_with_cors` → `cors_middleware` / `is_origin_allowed`.
   `deploy/aws/caddy/Caddyfile`: `X-Frame-Options` changed `DENY` →
   `SAMEORIGIN` and `Content-Security-Policy "frame-ancestors 'self'"` added so
   the deployed site can embed its own app iframes (explorer / playground /
   starbridge shells). The Caddyfile already serves the site and proxies the
   node API on the SAME origin, so the recommended path is CORS-free
   (same-origin needs no `--cors-origin`); the flag/env is only for clients that
   hit the node on a different origin.

### Verification (live local node)

```
healthy: true   dag_height: 34   latest_height: 0   block_count: 34
/api/cells: 4 cells (faucet 1,000,000 + alice/bob/carol)
Origin: https://devnet.example.com  → access-control-allow-origin echoed (when configured)
Origin: http://localhost:3000       → echoed (always)
Origin: https://evil.example.com    → no ACAO header (denied)
DREGG_CORS_ORIGINS env var path     → echoed; unconfigured node denies
```

## Remaining blockers (require live AWS / real secrets to verify)

These are no longer source-of-truth bugs in the deploy scripts. They are
operator inputs and live-host runtime facts that cannot be validated from this
checkout without an actual instance and real credentials.

1. Real secrets must be filled on the host.

   `setup.sh` now seeds `/etc/dregg/node.env` and `/etc/dregg/discord-bot.env`
   from the `.env.example` templates with placeholder (empty) values. Before the
   devnet is functional an operator must fill, on the host:

   - `/etc/dregg/node.env`: `DEVNET_PASSWORD` (the cipherclerk passphrase). The
     gateway starts without it but stays locked, so no `DEVNET_API_TOKEN` is
     issued and the bot/preflight token chain cannot complete.
   - `/etc/dregg/discord-bot.env`: `DISCORD_TOKEN`, `DISCORD_APP_ID`,
     `BOT_SECRET`, `FEDERATION_ID`. `setup.sh` enables `dregg-discord-bot` but
     only starts it when these four are non-empty (placeholder values would
     crash-loop the bot).

2. DNS / TLS / security-group facts are external.

   Caddy obtains certs for `devnet.dregg.fg-goose.online` and
   `dregg.fg-goose.online`; those records must resolve to the instance and ports
   80/443 (and UDP 9420 for gossip) must be open. Not verifiable from the repo.

3. Prebuilt static-site artifacts must be present on the host.

   `deploy-site.sh` refuses to proceed unless `site/dist` contains
   `index.html`, `explorer/index.html`, the WASM `pkg/` files, the two extension
   packages, and `artifacts-manifest.json` (or `BUILD_WEB_ARTIFACTS=1` with the
   full web toolchain available). On a fresh host these must be rsynced in, per
   the README. This lane does not own `site/`/`wasm/`/`extension/` artifact
   production.

## Resolved

1. ~~`dregg-node` does not compile from the current checkout.~~ **RESOLVED.**
   The node compiles and `get_federations` is defined in `node/src/api.rs`.
   `cargo run -q -p dregg-node -- run --help` succeeds.

2. ~~Fresh setup bootstraps from a stale GitHub repo identity.~~ **RESOLVED.**
   All `deploy/aws/*` repo references now use the canonical upstream remote
   `git@github.com:emberian/dregg.git` (the actual `origin` of this checkout).
   `setup.sh` clones from `DREGG_REPO_URL` (default that URL) into `REPO_DIR`
   (default `/opt/dregg`) on `BRANCH` (default `main`), and all subsequent paths
   are derived from `$REPO_DIR`. `deploy/aws/README.md` curl/clone snippets use
   `emberian/dregg` and document the override env var. `update.sh` already
   parameterizes `REPO_DIR`/`REMOTE`/`BRANCH` and uses the `origin` the clone
   created.

3. ~~Fresh setup does not create the `/etc/dregg` env files required by the
   bot/update/preflight path.~~ **RESOLVED.** `setup.sh` now creates
   `/etc/dregg` (0750, root:dregg) and seeds:
   - `/etc/dregg/node.env` from the new `deploy/aws/node.env.example`
     (`DEVNET_PASSWORD`, `DEVNET_API_TOKEN`), 0640 root:dregg, writable so
     `unlock-gateway.sh`'s in-place token rewrite (mktemp+mv in the same dir)
     succeeds.
   - `/etc/dregg/discord-bot.env` from `deploy/aws/discord-bot.env.example`,
     same perms.
   Both are created before the gateway starts, so the
   `EnvironmentFile=-/etc/dregg/node.env` read, the `ExecStartPost`
   `unlock-gateway.sh` token write, and `preflight-discord-bot.sh`'s
   `discord-bot.env` requirement all have their files present on a pristine host.

4. ~~`setup.sh` does not install or start the Discord bot service.~~
   **RESOLVED.** `setup.sh` now installs `dregg-discord-bot.service`, creates
   `/var/lib/dregg-discord-bot` (the sqlite db dir), `daemon-reload`s, and
   enables the bot. It starts the bot when the four required secrets are filled,
   otherwise leaves it enabled-but-stopped with an operator instruction. This
   matches `update.sh`, which installs/restarts both units and runs preflight,
   so a host stood up by either path converges to the same unit set.

## Reviewed assumptions (re-verified 2026-05-28)

- `deploy/aws/dregg-gateway.service` CLI flags match the current
  `dregg-node run` parser. Confirmed via `cargo run -q -p dregg-node -- run
  --help`: `--data-dir`, `--port`, `--bind`, `--node-index`,
  `--federation-size`, `--enable-pruning`, `--enable-faucet`,
  `--federation-mode`, and `--consensus` are all accepted.
- `deploy/aws/caddy/Caddyfile` proxies node surfaces to `localhost:8420` and the
  Discord bot read surface (`/discord-bot/api/*`,
  `/discord-bot/observability/stream`) to `localhost:8080`, matching
  `deploy/aws/discord-bot.env.example` (`HTTP_HOST=127.0.0.1`, `HTTP_PORT=8080`)
  and the gateway unit's `--port 8420`.
- `deploy-site.sh` expects prebuilt `site/dist` artifacts plus
  `site/dist/artifacts-manifest.json` unless `BUILD_WEB_ARTIFACTS=1` and the web
  toolchain are present. (See remaining blocker 3.)

## Checks run (2026-05-28)

```bash
bash -n deploy/aws/setup.sh deploy/aws/update.sh deploy/aws/deploy-site.sh \
  deploy/aws/preflight-discord-bot.sh
sh -n deploy/aws/unlock-gateway.sh
shellcheck deploy/aws/setup.sh deploy/aws/update.sh deploy/aws/deploy-site.sh \
  deploy/aws/preflight-discord-bot.sh deploy/aws/unlock-gateway.sh \
  scripts/build-web-artifacts.sh scripts/test-devnet-cluster.sh \
  scripts/no-unchecked-auth.sh
cargo run -q -p dregg-node -- run --help
```

Results:

- Bash/POSIX syntax checks passed for every script.
- ShellCheck: clean on all `deploy/aws/*` scripts; only the pre-existing
  informational findings remain in `scripts/test-devnet-cluster.sh` (`SC2329`,
  `SC2086`), which this lane did not modify.
- `cargo run -q -p dregg-node -- run --help` succeeds and confirms the gateway
  unit's flags.
