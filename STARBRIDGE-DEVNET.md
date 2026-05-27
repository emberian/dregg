# Devnet Deployment Preflight - 2026-05-26

Scope: fresh commonquant-ember AWS devnet deploy from the current checkout. No SSH
or deploy was performed.

## Hard blockers

1. `dregg-node` does not compile from the current checkout.

   Verification command:

   ```bash
   cargo run -q -p dregg-node -- run --help
   ```

   Result:

   ```text
   error[E0425]: cannot find value `get_federations` in this scope
       --> node/src/api.rs:1104:40
        |
   1104 |         .route("/api/federations", get(get_federations))
        |                                        ^^^^^^^^^^^^^^^
   ```

   A fresh deploy cannot pass `deploy/aws/setup.sh` or `deploy/aws/update.sh`
   because both run:

   ```bash
   cargo build --release -p dregg-node -p dregg-discord-bot
   ```

2. Fresh setup still bootstraps from the old GitHub repo identity.

   `deploy/aws/setup.sh` and `deploy/aws/README.md` clone/fetch
   `git@github.com:emberian/dregg.git` or
   `https://raw.githubusercontent.com/emberian/dregg/main/...`. If the intended
   source of truth for this deploy is `/Users/ember/dev/breadstuffs`, the fresh
   host instructions will deploy a different repository unless that remote is
   intentionally still canonical.

3. Fresh setup does not create the `/etc/dregg` env files required by the current
   bot/update/preflight path.

   `deploy/aws/dregg-gateway.service` has:

   ```ini
   EnvironmentFile=-/etc/dregg/node.env
   ExecStartPost=+/opt/dregg/deploy/aws/unlock-gateway.sh
   ```

   `deploy/aws/unlock-gateway.sh` exits without unlocking unless
   `DEVNET_PASSWORD` is present. On successful unlock it writes
   `DEVNET_API_TOKEN` into `/etc/dregg/node.env` and
   `/etc/dregg/discord-bot.env`, but only if those files already exist and are
   writable.

   `deploy/aws/preflight-discord-bot.sh` then requires `/etc/dregg/discord-bot.env`
   and requires `DEVNET_API_TOKEN` to be populated. A pristine host has no
   script-created `/etc/dregg` directory, no `/etc/dregg/node.env`, and no filled
   `/etc/dregg/discord-bot.env`, so the unlock/token/preflight chain cannot pass
   without manual operator setup.

4. `deploy/aws/setup.sh` does not install or start the Discord bot service, while
   the update/preflight path assumes it exists.

   `deploy/aws/update.sh` installs `dregg-discord-bot.service`, restarts it, and
   runs `deploy/aws/preflight-discord-bot.sh`. First-time setup only installs
   `dregg-gateway.service`, Caddy, and the static site. A fresh host will not have
   the bot systemd unit enabled from setup alone.

## Reviewed assumptions

- `deploy/aws/dregg-gateway.service` CLI flags match the current
  `node/src/main.rs` `dregg-node run` parser: `--data-dir`, `--port`, `--bind`,
  `--node-index`, `--federation-size`, `--enable-pruning`, `--enable-faucet`,
  `--federation-mode`, and `--consensus` are accepted by the source.
- `deploy/aws/caddy/Caddyfile` proxies the node surfaces to `localhost:8420` and
  the Discord bot read surface to `localhost:8080`, which matches
  `deploy/aws/discord-bot.env.example` (`HTTP_HOST=127.0.0.1`, `HTTP_PORT=8080`).
- The current static-site deploy path expects prebuilt `site/dist` artifacts and
  `site/dist/artifacts-manifest.json` unless `BUILD_WEB_ARTIFACTS=1` is set and
  the full web toolchain is available on the host.

## Checks run

```bash
bash -n deploy/aws/setup.sh deploy/aws/update.sh deploy/aws/deploy-site.sh \
  deploy/aws/preflight-discord-bot.sh scripts/build-web-artifacts.sh \
  scripts/test-devnet-cluster.sh scripts/no-unchecked-auth.sh
sh -n deploy/aws/unlock-gateway.sh
shellcheck deploy/aws/setup.sh deploy/aws/update.sh deploy/aws/deploy-site.sh \
  deploy/aws/preflight-discord-bot.sh deploy/aws/unlock-gateway.sh \
  scripts/build-web-artifacts.sh scripts/test-devnet-cluster.sh \
  scripts/no-unchecked-auth.sh
cargo run -q -p dregg-node -- run --help
```

Results:

- Bash/POSIX syntax checks passed.
- ShellCheck found only informational findings in `scripts/test-devnet-cluster.sh`
  (`SC2329`, `SC2086`), not in the AWS deploy scripts.
- The cargo check failed on the missing `get_federations` handler above.

