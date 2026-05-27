#!/bin/bash
# dregg gateway node — initial setup for AWS Graviton (Ubuntu/AL2023)
# Run once on a fresh instance.
set -euo pipefail

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
if [ ! -d /opt/dregg ]; then
  sudo mkdir -p /opt/dregg
  sudo chown "$(whoami)" /opt/dregg
  git clone git@github.com:emberian/dregg.git /opt/dregg
fi

cd /opt/dregg
git pull origin main
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
  /opt/dregg/target/release/dregg-node init --data-dir /opt/dregg-data
  sudo chown -R dregg:dregg /opt/dregg-data
fi

# Deploy genesis state (first run only)
if [ ! -f /opt/dregg-data/genesis.json ]; then
  echo "Deploying genesis state..."
  if [ -f /opt/dregg/deploy/genesis/genesis.json ]; then
    sudo cp /opt/dregg/deploy/genesis/genesis.json /opt/dregg-data/genesis.json
    sudo chown dregg:dregg /opt/dregg-data/genesis.json
    echo "  Genesis state installed from deploy/genesis/genesis.json"
  else
    echo "  WARNING: No genesis.json found. Run deploy/genesis/generate.sh first."
    echo "  The node will start without pre-configured state."
  fi
fi

# Install systemd service
sudo cp /opt/dregg/deploy/aws/dregg-gateway.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable dregg-gateway
sudo systemctl start dregg-gateway

# Install Caddy config
sudo mkdir -p /etc/caddy
sudo cp /opt/dregg/deploy/aws/caddy/Caddyfile /etc/caddy/Caddyfile
sudo systemctl enable caddy
sudo systemctl restart caddy

# Build and deploy static site assets
/opt/dregg/deploy/aws/deploy-site.sh

echo "=== Setup complete ==="
echo "Gateway node running on port 8420"
echo "Caddy reverse proxy handling HTTPS on port 443"
echo "Check status: sudo systemctl status dregg-gateway"
