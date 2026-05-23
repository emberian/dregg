#!/bin/bash
# pyana gateway node — initial setup for AWS Graviton (Ubuntu/AL2023)
# Run once on a fresh instance.
set -euo pipefail

echo "=== pyana gateway node setup ==="

# Install Rust
if ! command -v rustup &>/dev/null; then
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
  source "$HOME/.cargo/env"
fi
rustup toolchain install nightly
rustup default nightly

# Install system deps
if command -v apt-get &>/dev/null; then
  sudo apt-get update && sudo apt-get install -y \
    build-essential pkg-config libssl-dev \
    debian-keyring debian-archive-keyring apt-transport-https curl
elif command -v dnf &>/dev/null; then
  sudo dnf groupinstall -y "Development Tools"
  sudo dnf install -y openssl-devel pkg-config
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
if [ ! -d /opt/pyana ]; then
  sudo mkdir -p /opt/pyana
  sudo chown "$(whoami)" /opt/pyana
  git clone git@github.com:emberian/pyana.git /opt/pyana
fi

cd /opt/pyana
git pull origin main
cargo build --release -p pyana-node

# Create pyana user (runs the node process)
if ! id pyana &>/dev/null; then
  sudo useradd --system --no-create-home --shell /usr/sbin/nologin pyana
fi

# Create data directory
sudo mkdir -p /opt/pyana-data
sudo chown pyana:pyana /opt/pyana-data

# Generate node identity (first run only)
if [ ! -f /opt/pyana-data/node.key ]; then
  echo "Generating node identity..."
  /opt/pyana/target/release/pyana-node init --data-dir /opt/pyana-data
  sudo chown -R pyana:pyana /opt/pyana-data
fi

# Deploy genesis state (first run only)
if [ ! -f /opt/pyana-data/genesis.json ]; then
  echo "Deploying genesis state..."
  if [ -f /opt/pyana/deploy/genesis/genesis.json ]; then
    sudo cp /opt/pyana/deploy/genesis/genesis.json /opt/pyana-data/genesis.json
    sudo chown pyana:pyana /opt/pyana-data/genesis.json
    echo "  Genesis state installed from deploy/genesis/genesis.json"
  else
    echo "  WARNING: No genesis.json found. Run deploy/genesis/generate.sh first."
    echo "  The node will start without pre-configured state."
  fi
fi

# Install systemd service
sudo cp /opt/pyana/deploy/aws/pyana-gateway.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable pyana-gateway
sudo systemctl start pyana-gateway

# Install Caddy config
sudo mkdir -p /etc/caddy
sudo cp /opt/pyana/deploy/aws/caddy/Caddyfile /etc/caddy/Caddyfile
sudo systemctl enable caddy
sudo systemctl restart caddy

# Deploy static site assets
sudo mkdir -p /opt/pyana/site/explorer /opt/pyana/site/playground
sudo cp -r /opt/pyana/site/explorer/* /opt/pyana/site/explorer/ 2>/dev/null || true
sudo cp -r /opt/pyana/site/playground/* /opt/pyana/site/playground/ 2>/dev/null || true

echo "=== Setup complete ==="
echo "Gateway node running on port 8420"
echo "Caddy reverse proxy handling HTTPS on port 443"
echo "Check status: sudo systemctl status pyana-gateway"
