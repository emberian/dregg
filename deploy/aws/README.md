# `dregg` Gateway Node — AWS Graviton Deployment

Always-on gateway node for the dregg federation. Runs on an AWS Graviton instance
in the commonquant-ember account, providing a stable HTTPS/WSS endpoint for browser
clients and a permanent peer for ephemeral GitHub Actions federation nodes.

## Architecture

```
Internet
  │
  ├── Browser/Extension ──► https://devnet.dregg.fg-goose.online (Caddy TLS)
  │                              │
  │                              ├── /api/*     → dregg-node :8420
  │                              ├── /ws        → dregg-node :8420 (WebSocket)
  │                              ├── /explorer  → static files
  │                              └── /playground → static files
  │
  └── GitHub Actions nodes ──► devnet.dregg.fg-goose.online:9420 (QUIC gossip)
```

## Prerequisites

- AWS Graviton instance (t4g.small or larger) with Ubuntu 22.04+ or AL2023
- Domain `devnet.dregg.fg-goose.online` pointing to the instance's public IP
- Ports open: 80 (HTTP, for ACME), 443 (HTTPS), 8420 (HTTP API, optional direct), 9420 (QUIC gossip)
- SSH access configured
- GitHub deploy key for the dregg repo

## First-Time Setup

```bash
ssh ubuntu@devnet.dregg.fg-goose.online
curl -sSL https://raw.githubusercontent.com/emberian/dregg/main/deploy/aws/setup.sh | bash
```

Or if you prefer to inspect first:

```bash
ssh ubuntu@devnet.dregg.fg-goose.online
git clone git@github.com:emberian/dregg.git /tmp/dregg-setup
less /tmp/dregg-setup/deploy/aws/setup.sh
bash /tmp/dregg-setup/deploy/aws/setup.sh
```

## Updating

```bash
ssh ubuntu@devnet.dregg.fg-goose.online
bash /opt/dregg/deploy/aws/update.sh
```

The update script refuses to deploy over local or untracked changes. It fetches
`origin/main`, fast-forwards the checkout, builds both `dregg-node` and
`dregg-discord-bot`, restarts both systemd services, updates Caddy when needed,
and runs `deploy/aws/preflight-discord-bot.sh`.

## Static Site Artifacts

The public site is served from `site/dist`, not raw `site/` sources. Build the
browser artifacts in dependency order before copying to the server:

```bash
./scripts/build-web-artifacts.sh
rsync -az --delete site/dist/ ubuntu@devnet.dregg.fg-goose.online:/opt/dregg/site/dist/
ssh ubuntu@devnet.dregg.fg-goose.online /opt/dregg/deploy/aws/deploy-site.sh
```

That script rebuilds `wasm/pkg`, refreshes `site/pkg`, packages the Cipherclerk
extension downloads, rebuilds `site/dist`, and writes
`site/dist/artifacts-manifest.json` with SHA-256 checksums for the WASM and
extension packages. The server deploy refuses to proceed if those artifacts or
the manifest are missing. If the server has the full web toolchain, set
`BUILD_WEB_ARTIFACTS=1` before running `deploy-site.sh`; otherwise the server
uses the prebuilt `site/dist` uploaded by rsync.

## Monitoring

```bash
# Service status
sudo systemctl status dregg-gateway

# Logs (live)
sudo journalctl -u dregg-gateway -f

# Last 100 lines
sudo journalctl -u dregg-gateway -n 100 --no-pager

# Caddy logs
sudo journalctl -u caddy -f

# Health check
curl https://devnet.dregg.fg-goose.online/status
```

## Ports

| Port | Protocol | Purpose |
|------|----------|---------|
| 80   | TCP      | Caddy ACME challenge (auto-redirects to 443) |
| 443  | TCP      | HTTPS (Caddy reverse proxy, auto Let's Encrypt) |
| 8420 | TCP      | dregg-node HTTP API (direct, optional) |
| 9420 | UDP      | QUIC gossip (federation peer protocol) |

## Security Group (AWS)

Inbound rules:
- TCP 80 from 0.0.0.0/0 (ACME)
- TCP 443 from 0.0.0.0/0 (HTTPS)
- UDP 9420 from 0.0.0.0/0 (QUIC gossip)
- TCP 22 from your IP (SSH)

## Relay Operator Deployment

To run a relay operator alongside (or instead of) the gateway node:

```bash
# Start the relay operator service on port 3100
dregg-node relay \
  --bond 10000 \
  --port 3100 \
  --data-dir /opt/dregg-data \
  --state-file /opt/dregg-data/relay-state.json \
  --gc-interval 300 \
  --message-ttl 1000 \
  --max-capacity 100000
```

### Systemd Unit (dregg-relay.service)

Create `/etc/systemd/system/dregg-relay.service`:

```ini
[Unit]
Description=Dregg Relay Operator
After=network-online.target
Wants=network-online.target

[Service]
Type=simple
User=dregg
ExecStart=/opt/dregg/target/release/dregg-node relay \
  --bond 10000 \
  --port 3100 \
  --data-dir /opt/dregg-data \
  --state-file /opt/dregg-data/relay-state.json
Restart=always
RestartSec=5

[Install]
WantedBy=multi-user.target
```

```bash
sudo systemctl daemon-reload
sudo systemctl enable --now dregg-relay
```

### Caddy Configuration (add to Caddyfile)

```
handle /relay/* {
    reverse_proxy localhost:3100
}
```

### Relay Ports

| Port | Protocol | Purpose |
|------|----------|---------|
| 3100 | TCP      | Relay operator HTTP API |

Add to the security group:
- TCP 3100 from 0.0.0.0/0 (relay API) -- or restrict to known senders

### Monitoring

```bash
# Check relay status
curl http://localhost:3100/relay/status

# Service logs
sudo journalctl -u dregg-relay -f
```

## Troubleshooting

**Node won't start:**
```bash
sudo journalctl -u dregg-gateway -n 50 --no-pager
# Check data dir permissions
ls -la /opt/dregg-data/
```

**TLS certificate issues:**
```bash
sudo journalctl -u caddy -n 50 --no-pager
# Ensure port 80 is open for ACME challenges
sudo ss -tlnp | grep :80
```

**Federation peers can't connect:**
```bash
# Check QUIC port is open
sudo ss -ulnp | grep :9420
# Check firewall
sudo ufw status
```

**Out of disk:**
```bash
df -h
# Prune old data if needed
sudo systemctl stop dregg-gateway
# The node supports pruning, but manual cleanup:
du -sh /opt/dregg-data/*
sudo systemctl start dregg-gateway
```
