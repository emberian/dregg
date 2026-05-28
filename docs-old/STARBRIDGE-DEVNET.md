# Devnet Deployment Preflight - 2026-05-26 (updated 2026-05-28)

Scope: fresh commonquant-ember AWS devnet deploy from the current checkout. No SSH
or deploy was performed.

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
   `git@github.com:emberian/pyana.git` (the actual `origin` of this checkout).
   `setup.sh` clones from `DREGG_REPO_URL` (default that URL) into `REPO_DIR`
   (default `/opt/dregg`) on `BRANCH` (default `main`), and all subsequent paths
   are derived from `$REPO_DIR`. `deploy/aws/README.md` curl/clone snippets use
   `emberian/pyana` and document the override env var. `update.sh` already
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
