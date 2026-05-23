# Pyana Gateway Node — AWS Graviton Deployment

Always-on gateway node for the pyana federation. Runs on an AWS Graviton instance
in the commonquant-ember account, providing a stable HTTPS/WSS endpoint for browser
clients and a permanent peer for ephemeral GitHub Actions federation nodes.

## Architecture

```
Internet
  │
  ├── Browser/Extension ──► https://devnet.pyana.fg-goose.online (Caddy TLS)
  │                              │
  │                              ├── /api/*     → pyana-node :8420
  │                              ├── /ws        → pyana-node :8420 (WebSocket)
  │                              ├── /explorer  → static files
  │                              └── /playground → static files
  │
  └── GitHub Actions nodes ──► devnet.pyana.fg-goose.online:9420 (QUIC gossip)
```

## Prerequisites

- AWS Graviton instance (t4g.small or larger) with Ubuntu 22.04+ or AL2023
- Domain `devnet.pyana.fg-goose.online` pointing to the instance's public IP
- Ports open: 80 (HTTP, for ACME), 443 (HTTPS), 8420 (HTTP API, optional direct), 9420 (QUIC gossip)
- SSH access configured
- GitHub deploy key for the pyana repo

## First-Time Setup

```bash
ssh ubuntu@devnet.pyana.fg-goose.online
curl -sSL https://raw.githubusercontent.com/emberian/pyana/main/deploy/aws/setup.sh | bash
```

Or if you prefer to inspect first:

```bash
ssh ubuntu@devnet.pyana.fg-goose.online
git clone git@github.com:emberian/pyana.git /tmp/pyana-setup
less /tmp/pyana-setup/deploy/aws/setup.sh
bash /tmp/pyana-setup/deploy/aws/setup.sh
```

## Updating

```bash
ssh ubuntu@devnet.pyana.fg-goose.online
bash /opt/pyana/deploy/aws/update.sh
```

## Monitoring

```bash
# Service status
sudo systemctl status pyana-gateway

# Logs (live)
sudo journalctl -u pyana-gateway -f

# Last 100 lines
sudo journalctl -u pyana-gateway -n 100 --no-pager

# Caddy logs
sudo journalctl -u caddy -f

# Health check
curl https://devnet.pyana.fg-goose.online/status
```

## Ports

| Port | Protocol | Purpose |
|------|----------|---------|
| 80   | TCP      | Caddy ACME challenge (auto-redirects to 443) |
| 443  | TCP      | HTTPS (Caddy reverse proxy, auto Let's Encrypt) |
| 8420 | TCP      | pyana-node HTTP API (direct, optional) |
| 9420 | UDP      | QUIC gossip (federation peer protocol) |

## Security Group (AWS)

Inbound rules:
- TCP 80 from 0.0.0.0/0 (ACME)
- TCP 443 from 0.0.0.0/0 (HTTPS)
- UDP 9420 from 0.0.0.0/0 (QUIC gossip)
- TCP 22 from your IP (SSH)

## Troubleshooting

**Node won't start:**
```bash
sudo journalctl -u pyana-gateway -n 50 --no-pager
# Check data dir permissions
ls -la /opt/pyana-data/
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
sudo systemctl stop pyana-gateway
# The node supports pruning, but manual cleanup:
du -sh /opt/pyana-data/*
sudo systemctl start pyana-gateway
```
