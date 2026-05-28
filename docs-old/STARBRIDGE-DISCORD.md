# Starbridge Discord Review

Date: 2026-05-26

## Decision

Do not kill or replace the running Discord bot or commonquant-ember devnet from the current tree yet.

`discord-bot` is a substantial prototype and it compiles, but it is not yet the complete, coherent, Discord-native "Starbridge via Discord" experience we want to put in front of users as the canonical Dragon's Egg Discord surface. The current deployment scripts also do not safely support a fresh bot plus devnet replacement: `deploy/` only manages the gateway node, the gateway systemd unit appears stale against the current CLI, and there is no checked-in bot service.

I ran:

```bash
cargo check -p dregg-discord-bot
```

Result: pass, with one local dead-code warning in `discord-bot/src/cipherclerk.rs`.

## What Is Already Strong

- Broad command surface: explorer, hosted cclerk, transfers, gallery, identity, presence, status, social, CapTP, queues, governance, names, and federation setup are all represented in `discord-bot/src/main.rs:86`.
- Sensitive flows mostly answer ephemerally, which is the right default for keys, addresses, balances, and private operational feedback.
- The explorer command has useful devnet browse affordances for cells, turns, blocks, notes, proofs, factories, search, stats, recent activity, watches, and feeds in `discord-bot/src/commands/explorer.rs:14`.
- Activity feeds and watcher DMs are real Discord-native primitives, with feed polling in `discord-bot/src/activity_feed.rs:27` and watcher notification in `discord-bot/src/activity_feed.rs:99`.
- Presence attestations are a promising Discord-specific Dragon's Egg feature, because Discord presence can become a dischargeable social caveat instead of just another wallet command.
- The bot has an HTTP read surface intended for Starbridge RemoteRuntime in `discord-bot/src/http_server.rs:108`, which is the right integration direction.

## No-Go Findings

### 1. Primary onboarding command is inconsistent

The README documents `/cipherclerk`, the dispatcher handles `"cipherclerk"`, but the command registration creates `/cclerk`:

- `discord-bot/README.md:39`
- `discord-bot/src/main.rs:151`
- `discord-bot/src/commands/cipherclerk.rs:14`

That means the advertised onboarding command is not coherent. A new user can hit the first command and fail.

### 2. Intent and handoff are placeholders, not implemented flows

The Starbridge plan calls out `/intent post`, `/handoff`, and reaction-to-fulfill flows. Current code does not register `/intent` or `/handoff`. Instead it registers `/status` a second time as a placeholder:

- duplicate placeholder registration: `discord-bot/src/main.rs:126`
- unregistered placeholder router arm: `discord-bot/src/main.rs:210`

This is the largest gap between "Starbridge via Discord" and the current bot. The core livedebugger/fork/replay/intent experience is not present.

### 3. CapTP is present but not safely user-bound

`/cap-share` and `/cap-revoke` accept arbitrary cell ids and call the bot-level CapTP client without checking that the Discord user owns or holds the capability:

- share handler: `discord-bot/src/commands/captp.rs:68`
- revoke handler: `discord-bot/src/commands/captp.rs:298`
- bot exporter identity: `discord-bot/src/captp_client.rs:73`

For a public Discord deployment, export/delegate/revoke must be holder-right checked and bound to the user identity mode.

### 4. External identity linking has no proof of ownership

`/link-cipherclerk` only validates that the address is 64 hex characters before storing it:

- link validation/storage: `discord-bot/src/commands/federation.rs:163`

But transfer signing still derives a hosted bot-secret key for the Discord user:

- hosted signing path: `discord-bot/src/commands/transfer.rs:140`

So linked external cells are not proven and may not be signable. The bot needs a clear distinction between hosted custodial identities and external linked identities, plus a challenge signature flow for linking.

### 5. Queue bridging is not actually connected to normal Discord messages

The event bridge can map Discord channels to dregg queues, and `message()` calls it:

- message event: `discord-bot/src/main.rs:223`
- event bridge link concept: `discord-bot/src/discord_caps.rs:253`

But queue commands post to node endpoints and do not persistently call the channel-linking bridge:

- queue create/publish/subscribe start: `discord-bot/src/commands/queue.rs:128`
- queue mount posts only to the node: `discord-bot/src/commands/queue.rs:372`

For Discord-as-Starbridge, a channel should become a live queue surface. Today that bridge is mostly conceptual.

### 6. The Starbridge HTTP surface is mostly placeholder data

The bot advertises itself as a Starbridge RemoteRuntime target, but the core reads are empty or synthetic:

- `/api/cells` returns an empty vector: `discord-bot/src/http_server.rs:161`
- `/api/receipts/recent` returns an empty vector: `discord-bot/src/http_server.rs:223`
- SSE sends `"bot-cell"` instead of the real bot cell: `discord-bot/src/http_server.rs:254`
- CORS is permissive while HTTP binds to `0.0.0.0` by default: `discord-bot/src/http_server.rs:118`, `discord-bot/src/config.rs:62`

Starbridge should be able to inspect the bot's known cells, receipts, capabilities, queue links, federations, recent activity, and held references. It cannot yet.

### 7. It is still mostly an API console inside Discord

The current UX is slash-command plus embed heavy. Discord is capable of much more:

- persistent dashboards
- buttons for accept, reject, revoke, vote, fulfill, fork, replay
- select menus for cells, names, queues, proposals, turns
- modals for proposal bodies, credential attributes, intent specs
- autocomplete for names, cells, queues, capabilities
- threads for proposals, auctions, disputes, handoffs, and intent fulfillment
- reaction or component-driven orchestration

Those are not polish. They are the difference between "commands that call dregg" and "Dragon's Egg inhabits Discord."

## Deploy Review

### Current gateway path

The AWS deployment docs target the commonquant-ember account and `https://devnet.dregg.fg-goose.online`:

- architecture and prerequisites: `deploy/aws/README.md:1`
- update flow: `deploy/aws/update.sh:7`
- Caddy proxy to node: `deploy/aws/caddy/Caddyfile:1`
- gateway service: `deploy/aws/dregg-gateway.service:11`

The normal update script does:

```bash
cd /opt/dregg
git fetch origin main
git reset --hard origin/main
cargo build --release -p dregg-node
sudo systemctl restart dregg-gateway
```

That is a node redeploy, not a bot redeploy.

### Bot deployment is missing

There is no `deploy/aws/dregg-discord-bot.service`, no bot environment file template, no Caddy route for the bot HTTP surface, and no update path that builds or restarts `dregg-discord-bot`.

The bot requires at least:

- `DISCORD_TOKEN`
- `DISCORD_APP_ID`
- `BOT_SECRET`
- `DEVNET_URL`
- `DATABASE_URL`
- `FEDERATION_ID`
- `HTTP_HOST`
- `HTTP_PORT`

See `discord-bot/src/config.rs:38`.

### Gateway redeploy is also risky right now

`deploy/aws/dregg-gateway.service` passes flags that appear stale against the current node CLI:

- `--morpheus`: `deploy/aws/dregg-gateway.service:14`
- `--prove-transitions`: `deploy/aws/dregg-gateway.service:17`

The update script also uses `git reset --hard origin/main` in `/opt/dregg`, which will discard remote hotfixes or local operational changes:

- `deploy/aws/update.sh:7`

Genesis handling is not ready for a confident reset either. The checked-in genesis file is documented as placeholder-key devnet material, while the runtime loader expects the current generated schema. A fresh commonquant-ember reset should first regenerate and stage a real devnet genesis and preserve generated secrets out of git.

## Target Experience

The desired bot should feel like a Discord-native Starbridge:

1. `/egg` or `/dregg` opens a persistent personal control panel.
2. The user's cell home shows balance, names, caps, notes, queues, recent turns, and current devnet status.
3. Public activity channels show rich live turn cards with buttons to inspect, fork, watch, fulfill, or open in Starbridge.
4. Cap handoffs use pasteable sturdy refs plus accept/reject buttons, expiry, revocation state, and holder proof checks.
5. Intents post as public cards in configured channels, with fulfill buttons, reaction shortcuts, thread logs, and receipt follow-up.
6. Governance proposals and namespace changes live in threads with vote buttons, modal rationale capture, and final receipts.
7. Queue-mounted Discord channels actually bridge regular messages into dregg queues, with policy/capability status visible in-channel.
8. Every object card includes "open in Starbridge" links and the bot HTTP surface exposes the same objects to RemoteRuntime.
9. The bot never fabricates protocol state; unavailable live data is shown as unavailable with the exact endpoint or capability missing.

## Implementation Plan

### Phase 0: Do not deploy

- Leave the current remote bot/devnet alone.
- Do not run `deploy/aws/update.sh` until the service flags and genesis path are corrected.
- Do not register new global Discord commands from this tree until command parity is fixed.

### Phase 1: Coherence and safety

- Align `/cclerk` vs `/cipherclerk` naming across README, command registration, and dispatcher.
- Remove duplicate `/status` registration.
- Either implement or delete the `intent` and `handoff` router arms.
- Add command registration/router parity tests.
- Add hosted vs external identity mode to the database.
- Require proof-of-ownership for external links.
- Gate CapTP export/delegate/revoke by holder rights.
- Remove third-party QR generation for raw capability URIs.

### Phase 2: Discord-native UX

- Add a top-level `/dregg` dashboard command.
- Add component handlers for buttons, select menus, and modals.
- Convert transfers, cap accept/revoke, governance votes, queue subscribe, and intent fulfill into component-driven flows.
- Add autocomplete for known cells, names, queues, caps, and watched objects.
- Use threads for proposals, auctions, disputes, handoffs, and long-running intent fulfillment.

### Phase 3: Real Starbridge substrate

- Materialize the bot's known cells, watched cells, held caps, exports, queue links, receipts, and recent activity into SQLite.
- Back `/api/cells`, `/api/receipts/recent`, `/api/federations`, and `/observability/stream` with real state.
- Broadcast live Discord, CapTP, devnet, queue, and receipt events into SSE.
- Add `GET /api/capabilities`, `GET /api/intents/recent`, and `GET /api/activity/recent` for Starbridge RemoteRuntime parity.
- Add CORS and auth configuration appropriate for public HTTP exposure.

### Phase 4: Deploy path

- Fix `deploy/aws/dregg-gateway.service` flags against the current `dregg-node run` CLI.
- Add `deploy/aws/dregg-discord-bot.service`.
- Add an environment file template with required bot secrets documented but not committed.
- Add a deployment script that builds both `dregg-node` and `dregg-discord-bot`, validates config, then restarts services in order.
- Add a preflight script that checks `curl /status`, bot HTTP `/api/federations`, `/api/cells`, Discord token presence, and Caddy routing before swapping live services.
- Generate a fresh devnet genesis in the runtime schema before any destructive reset.

## Go Criteria

Only replace the running commonquant-ember bot/devnet after all of these are true:

- `cargo check -p dregg-discord-bot` passes.
- Command registration matches the dispatcher and README.
- `/dregg` dashboard, identity onboarding, transfer, cap handoff, queue bridge, intent post, governance vote, and explorer flows are implemented with Discord components where appropriate.
- Starbridge HTTP endpoints expose real bot state, not empty vectors or synthetic ids.
- Bot systemd, env file, Caddy routing, and update scripts exist under `deploy/aws`.
- Gateway service flags are current.
- Fresh genesis has been generated and reviewed.
- A dry-run deploy on a disposable host passes health checks.

