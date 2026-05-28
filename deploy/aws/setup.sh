#!/bin/bash
# dregg gateway node — initial setup for AWS Graviton (Ubuntu/AL2023)
# Run once on a fresh instance.
set -euo pipefail

# Source repository. Override with DREGG_REPO_URL for a fork or mirror.
# Canonical default is the current upstream remote (git@github.com:emberian/pyana.git).
REPO_URL="${DREGG_REPO_URL:-git@github.com:emberian/pyana.git}"
REPO_DIR="${REPO_DIR:-/opt/dregg}"
BRANCH="${BRANCH:-main}"

echo "=== dregg gateway node setup ==="

# Install Rust
if ! command -v rustup &>/dev/null; then
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
  # shellcheck source=/dev/null
  source "$HOME/.cargo/env"
fi
rustup toolchain install nightly
rustup default nightly

# Install system deps
if command -v apt-get &>/dev/null; then
  sudo apt-get update && sudo apt-get install -y \
    build-essential pkg-config libssl-dev \
    debian-keyring debian-archive-keyring apt-transport-https curl jq
elif command -v dnf &>/dev/null; then
  sudo dnf groupinstall -y "Development Tools"
  sudo dnf install -y openssl-devel pkg-config jq
fi

# Install Caddy (HTTPS reverse proxy with automatic Let's Encrypt)
if ! command -v caddy &>/dev/null; then
  if command -v apt-get &>/dev/null; then
    curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/gpg.key' | sudo gpg --dearmor -o /usr/share/keyrings/caddy-stable-archive-keyring.gpg
    curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/debian.deb.txt' | sudo tee /etc/apt/sources.list.d/caddy-stable.list
    sudo apt-get update && sudo apt-get install -y caddy
  elif command -v dnf &>/dev/null; then
    sudo dnf install -y 'dnf-command(copr)'
    sudo dnf copr enable -y @caddy/caddy
    sudo dnf install -y caddy
  fi
fi

# Clone and build
if [ ! -d "$REPO_DIR" ]; then
  sudo mkdir -p "$REPO_DIR"
  sudo chown "$(whoami)" "$REPO_DIR"
  git clone "$REPO_URL" "$REPO_DIR"
fi

cd "$REPO_DIR"
git pull origin "$BRANCH"
cargo build --release -p dregg-node -p dregg-discord-bot

# Create dregg user (runs the node process)
if ! id dregg &>/dev/null; then
  sudo useradd --system --no-create-home --shell /usr/sbin/nologin dregg
fi

# Create data directory
sudo mkdir -p /opt/dregg-data
sudo chown dregg:dregg /opt/dregg-data

# Generate node identity (first run only)
if [ ! -f /opt/dregg-data/node.key ]; then
  echo "Generating node identity..."
  "$REPO_DIR/target/release/dregg-node" init --data-dir /opt/dregg-data
  sudo chown -R dregg:dregg /opt/dregg-data
fi

# Deploy genesis state (first run only)
if [ ! -f /opt/dregg-data/genesis.json ]; then
  echo "Deploying genesis state..."
  if [ -f "$REPO_DIR/deploy/genesis/genesis.json" ]; then
    sudo cp "$REPO_DIR/deploy/genesis/genesis.json" /opt/dregg-data/genesis.json
    sudo chown dregg:dregg /opt/dregg-data/genesis.json
    echo "  Genesis state installed from deploy/genesis/genesis.json"
  else
    echo "  WARNING: No genesis.json found. Run deploy/genesis/generate.sh first."
    echo "  The node will start without pre-configured state."
  fi
fi

# Seed /etc/dregg environment files.
#
# The gateway unit reads /etc/dregg/node.env (EnvironmentFile=-), and its
# ExecStartPost (unlock-gateway.sh) only unlocks the cipherclerk when
# DEVNET_PASSWORD is set there. On a successful unlock it writes the issued
# DEVNET_API_TOKEN back into both node.env and discord-bot.env, but only if
# those files already exist and are writable. The bot unit and
# preflight-discord-bot.sh both require discord-bot.env to exist. So a fresh
# host needs both files created up front (root-owned, 0640, group dregg) before
# the gateway starts.
echo "Seeding /etc/dregg environment files..."
sudo install -d -m 0750 -o root -g dregg /etc/dregg

if [ ! -f /etc/dregg/node.env ]; then
  if [ -f "$REPO_DIR/deploy/aws/node.env.example" ]; then
    sudo install -m 0640 -o root -g dregg \
      "$REPO_DIR/deploy/aws/node.env.example" /etc/dregg/node.env
  else
    printf '# Fill DEVNET_PASSWORD to enable automatic cipherclerk unlock.\nDEVNET_PASSWORD=\nDEVNET_API_TOKEN=\n' \
      | sudo install -m 0640 -o root -g dregg /dev/stdin /etc/dregg/node.env
  fi
  echo "  Created /etc/dregg/node.env — set DEVNET_PASSWORD then restart dregg-gateway."
fi

if [ ! -f /etc/dregg/discord-bot.env ]; then
  sudo install -m 0640 -o root -g dregg \
    "$REPO_DIR/deploy/aws/discord-bot.env.example" /etc/dregg/discord-bot.env
  echo "  Created /etc/dregg/discord-bot.env — fill DISCORD_TOKEN/DISCORD_APP_ID/BOT_SECRET/FEDERATION_ID."
fi

# unlock-gateway.sh runs as the gateway's ExecStartPost (with elevated privs via
# the leading '+') and rewrites these files in place via mktemp+mv, so the
# directory must be writable by root and the files must be writable for the
# token to land. install above guarantees that.

# Create the bot's state directory (sqlite db lives here per discord-bot.env).
sudo install -d -o dregg -g dregg /var/lib/dregg-discord-bot

# Install systemd services
sudo cp "$REPO_DIR/deploy/aws/dregg-gateway.service" /etc/systemd/system/dregg-gateway.service
sudo cp "$REPO_DIR/deploy/aws/dregg-discord-bot.service" /etc/systemd/system/dregg-discord-bot.service
sudo systemctl daemon-reload
sudo systemctl enable dregg-gateway
sudo systemctl start dregg-gateway

# Enable the Discord bot. It is only started once discord-bot.env carries real
# secrets; starting it with placeholder values would crash-loop. Enable so it
# comes up on the next boot / after the operator fills secrets and runs
# `sudo systemctl start dregg-discord-bot` (or deploy/aws/update.sh).
sudo systemctl enable dregg-discord-bot
if grep -Eq '^DISCORD_TOKEN=.+' /etc/dregg/discord-bot.env \
  && grep -Eq '^DISCORD_APP_ID=.+' /etc/dregg/discord-bot.env \
  && grep -Eq '^BOT_SECRET=.+' /etc/dregg/discord-bot.env \
  && grep -Eq '^FEDERATION_ID=.+' /etc/dregg/discord-bot.env; then
  sudo systemctl start dregg-discord-bot
else
  echo "  dregg-discord-bot enabled but not started: fill secrets in"
  echo "  /etc/dregg/discord-bot.env then 'sudo systemctl start dregg-discord-bot'."
fi

# Install Caddy config
sudo mkdir -p /etc/caddy
sudo cp "$REPO_DIR/deploy/aws/caddy/Caddyfile" /etc/caddy/Caddyfile
sudo systemctl enable caddy
sudo systemctl restart caddy

# Build and deploy static site assets
"$REPO_DIR/deploy/aws/deploy-site.sh"

echo "=== Setup complete ==="
echo "Gateway node running on port 8420"
echo "Caddy reverse proxy handling HTTPS on port 443"
echo "Check status: sudo systemctl status dregg-gateway"
echo "Bot status:   sudo systemctl status dregg-discord-bot"
