# Devnet Upgrade Plan: Multi-Service AWS Deployment

## 1. Current State Assessment

### What Exists

**Docker (`docker/`)**
- `Dockerfile` — single-stage build of `pyana-node` only (nightly-2026-01-01, debian:bookworm-slim runtime)
- `docker-compose.yml` — 3-node federation (node-0/1/2) + nginx explorer on :3000
- `start-devnet.sh` — generates genesis, builds image, docker-compose up
- No ARM64 support (no multi-arch build, no `--platform` directives)
- No app services (gallery, bounty-board, compute-exchange) in compose

**AWS Deploy (`deploy/aws/`)**
- Full setup for a single Graviton gateway node at `devnet.pyana.fg-goose.online`
- `setup.sh` — installs Rust, Caddy, builds from source on-instance, creates systemd unit
- `update.sh` — git pull, cargo build, systemd restart
- `pyana-gateway.service` — runs pyana-node with `--federation-size 4 --node-index 0 --prove-transitions --enable-pruning --enable-faucet`
- `caddy/Caddyfile` — reverse proxy for API, WS, federation, static site (explorer, playground)
- No Docker on the Graviton instance (builds from source directly)
- No gallery/bounty-board/compute-exchange deployment
- No log aggregation or metrics scraping configured

**GitHub Actions (`.github/workflows/`)**
- `ci.yml` — check, test (ubuntu+macos), clippy, fmt, audit. Solid.
- `federation-node-{1,2,3}.yml` — ephemeral nodes on GHA runners, each runs ~5h45m on 5h cron. Peer with gateway via QUIC.
- `intent-service.yml` — same pattern as federation nodes
- `discovery.yml` — assembles discovery.json from node state. **Pushes to both `federation-state` (orphan branch) AND `main`** (the main push is the bug)
- `pages.yml` — builds WASM + paper + extension, deploys to GitHub Pages
- `demos.yml` — runs all demo examples, publishes results.json to Pages
- `nightly.yml` — tests plonky3 feature
- `bench.yml` — criterion benchmarks (manual dispatch only)

**Local Dev (`scripts/test-devnet-cluster.sh`)**
- Runs 3 nodes + optional bounty-board + compute-exchange as bare processes
- Health checks, faucet test, propagation check
- Works but no gallery, no frontend, no hot-reload

### What Works
- Single gateway node on Graviton (devnet.pyana.fg-goose.online) is operational
- GitHub Actions federation nodes peer with gateway correctly
- Federation state stored on orphan branch `federation-state` correctly
- CI pipeline (check/test/clippy/fmt/audit) is complete
- Local devnet script boots and validates 3-node cluster

### What's Broken or Missing
1. **Discovery pushes to main** — `discovery.yml` lines 159-166 commit to main, creating noise. Should only go to `federation-state` branch.
2. **No multi-arch Docker image** — Dockerfile has no ARM64 support; can't deploy pre-built images to Graviton.
3. **No app services in Docker** — gallery, bounty-board, compute-exchange are absent from docker-compose.
4. **Gateway builds from source** — 15+ minute rebuild on t4g.small, no rollback capability, no image pinning.
5. **No metrics/monitoring** — `/metrics` endpoint exists on nodes but nothing scrapes it.
6. **No CI-triggered deployment** — update.sh is manual SSH.
7. **docker/devnet-config/ doesn't exist** — compose references it but it's gitignored/generated at runtime.

---

## 2. Target Architecture

```
                         Internet
                            |
              +-------------+-------------+
              |                           |
     devnet.pyana.fg-goose.online         GitHub Pages
       (Graviton t4g.medium)         (static)
              |
     +--------+--------+
     |     Caddy        |  TLS termination, routing
     +--------+---------+
              |
     +--------+------------------------------------------+
     |        |            |             |               |
  pyana-node  gallery   bounty-board  compute-exch   [future apps]
  :8420       :8430     :8440         :8450
  (federation (Axum)    (Axum)        (Axum)
   consensus,
   faucet, API)
     |
     | QUIC :9420
     |
  +--+--+--+--+
  |  |  |  |  |
 GHA GHA GHA  (future nodes)
 n1  n2  n3
```

**Networking:**
- Caddy handles TLS + routing (already works)
- New routes: `/gallery/*` -> :8430, `/bounty/*` -> :8440, `/compute/*` -> :8450
- QUIC :9420 unchanged (federation gossip)
- Each app service connects to local pyana-node at 127.0.0.1:8420

**Service Management:**
- Docker Compose on the Graviton instance (replaces bare cargo build)
- Multi-arch images built in CI, pushed to GHCR
- Systemd only manages Docker Compose (single unit)
- Each service is a container with restart policy

---

## 3. AWS Deployment Plan

### Instance Sizing

| Component | Resource Need |
|-----------|-------------|
| pyana-node (consensus + proofs) | ~1.5 GB RAM, 2 vCPU |
| gallery | ~128 MB RAM |
| bounty-board | ~128 MB RAM |
| compute-exchange | ~128 MB RAM |
| Caddy | ~64 MB RAM |
| Docker overhead | ~256 MB |
| **Total** | **~2.5 GB RAM, 2 vCPU** |

**Recommendation:** `t4g.medium` (2 vCPU, 4 GB RAM, ARM64 Graviton2). ~$24/month on-demand, ~$15/month reserved.

If `--prove-transitions` is CPU-heavy during proof generation, consider `t4g.large` (2 vCPU, 8 GB) for extra headroom.

### Docker Configuration

New multi-service `docker-compose.prod.yml`:

```yaml
services:
  node:
    image: ghcr.io/emberian/pyana-node:latest
    command: run --data-dir /data --port 8420 --gossip-port 9420
      --morpheus --node-index 0 --federation-size 4
      --prove-transitions --enable-pruning --enable-faucet
    volumes:
      - node-data:/data
    ports:
      - "8420:8420"
      - "9420:9420/udp"
    restart: unless-stopped
    environment:
      - RUST_LOG=info
      - PYANA_GATEWAY=true

  gallery:
    image: ghcr.io/emberian/pyana-gallery:latest
    command: --node-url http://node:8420 --listen 0.0.0.0:8430
    ports:
      - "127.0.0.1:8430:8430"
    depends_on: [node]
    restart: unless-stopped

  bounty-board:
    image: ghcr.io/emberian/pyana-bounty-board:latest
    command: --node-url http://node:8420 --listen 0.0.0.0:8440
    ports:
      - "127.0.0.1:8440:8440"
    depends_on: [node]
    restart: unless-stopped

  compute-exchange:
    image: ghcr.io/emberian/pyana-compute-exchange:latest
    command: --node-url http://node:8420 --listen 0.0.0.0:8450
    ports:
      - "127.0.0.1:8450:8450"
    depends_on: [node]
    restart: unless-stopped

volumes:
  node-data:
```

### Networking (Security Groups)

Keep existing rules, add nothing new (apps bind to 127.0.0.1, only Caddy is public):

| Port | Protocol | Source | Purpose |
|------|----------|--------|---------|
| 80 | TCP | 0.0.0.0/0 | ACME challenge |
| 443 | TCP | 0.0.0.0/0 | HTTPS (Caddy) |
| 9420 | UDP | 0.0.0.0/0 | QUIC gossip |
| 22 | TCP | admin IP | SSH |

### Secrets Management

- Node key: stored at `/opt/pyana-data/node.key` (already exists, persist across deploys)
- No AWS Secrets Manager needed for single-node — key stays on disk, volume-mounted
- GitHub Actions deployment: use OIDC role assumption (`aws-actions/configure-aws-credentials`) with `commonquant-ember` profile
- Deploy key for GHCR pull: instance IAM role or `docker login ghcr.io` with PAT stored in `/root/.docker/config.json`

### Updated Caddyfile (additions)

```
    # Gallery app
    handle /gallery/* {
        uri strip_prefix /gallery
        reverse_proxy localhost:8430
    }

    # Bounty board
    handle /bounty/* {
        uri strip_prefix /bounty
        reverse_proxy localhost:8440
    }

    # Compute exchange
    handle /compute/* {
        uri strip_prefix /compute
        reverse_proxy localhost:8450
    }

    # Metrics (internal only — restrict to VPC or admin IP)
    handle /metrics {
        reverse_proxy localhost:8420
    }
```

---

## 4. GitHub Actions Fixes

### 4.1 Discovery Workflow — Remove Main Push

The `discovery.yml` workflow currently pushes to both `federation-state` AND `main`. Remove lines 150-166 (the "Commit and push discovery.json to main" step). The site can fetch discovery.json from `federation-state` branch via raw URL or the Pages build can pull it in.

**Specifically delete:**
```yaml
      - name: Check for changes on main
        ...
      - name: Commit and push discovery.json to main
        ...
```

### 4.2 Multi-Arch Docker Build Workflow (New)

Add `.github/workflows/docker.yml`:

```yaml
name: Build & Push Docker Images

on:
  push:
    branches: [main]
    paths:
      - "node/**"
      - "apps/**"
      - "app-framework/**"
      - "Cargo.toml"
      - "Cargo.lock"
      - "docker/Dockerfile*"
  workflow_dispatch:

jobs:
  build-images:
    runs-on: ubuntu-latest
    permissions:
      contents: read
      packages: write
    strategy:
      matrix:
        target:
          - { package: pyana-node, image: pyana-node }
          - { package: pyana-gallery, image: pyana-gallery }
          - { package: pyana-bounty-board, image: pyana-bounty-board }
          - { package: compute-exchange, image: pyana-compute-exchange }
    steps:
      - uses: actions/checkout@v4
      - uses: docker/setup-qemu-action@v3
      - uses: docker/setup-buildx-action@v3
      - uses: docker/login-action@v3
        with:
          registry: ghcr.io
          username: ${{ github.actor }}
          password: ${{ secrets.GITHUB_TOKEN }}
      - uses: docker/build-push-action@v6
        with:
          context: .
          file: docker/Dockerfile.multi
          platforms: linux/amd64,linux/arm64
          push: true
          tags: ghcr.io/emberian/${{ matrix.target.image }}:latest,ghcr.io/emberian/${{ matrix.target.image }}:${{ github.sha }}
          build-args: |
            PACKAGE=${{ matrix.target.package }}
          cache-from: type=gha
          cache-to: type=gha,mode=max
```

### 4.3 New Multi-Target Dockerfile (`docker/Dockerfile.multi`)

```dockerfile
FROM rust:latest AS builder
ARG PACKAGE=pyana-node
ARG TARGETPLATFORM
RUN rustup toolchain install nightly-2026-01-01 && rustup default nightly-2026-01-01
WORKDIR /build
COPY . .
RUN cargo build --release -p ${PACKAGE}
RUN cp target/release/$(echo ${PACKAGE} | tr '-' '_' | sed 's/pyana_//') /usr/local/bin/app || \
    cp target/release/${PACKAGE} /usr/local/bin/app || \
    find target/release -maxdepth 1 -type f -executable -name "*${PACKAGE}*" -exec cp {} /usr/local/bin/app \;

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /usr/local/bin/app /usr/local/bin/app
ENTRYPOINT ["app"]
```

Note: The binary name resolution needs testing — workspace crates produce binaries matching the package name with hyphens. The node binary is `pyana-node`, gallery is `pyana-gallery`, etc. A simpler approach:

```dockerfile
RUN cargo build --release -p ${PACKAGE} && \
    find target/release -maxdepth 1 -name "${PACKAGE}" -type f -executable | head -1 | xargs -I{} cp {} /usr/local/bin/app
```

### 4.4 Deployment Workflow (New)

Add `.github/workflows/deploy.yml`:

```yaml
name: Deploy to AWS

on:
  workflow_run:
    workflows: ["Build & Push Docker Images"]
    types: [completed]
    branches: [main]
  workflow_dispatch:

jobs:
  deploy:
    if: ${{ github.event.workflow_run.conclusion == 'success' || github.event_name == 'workflow_dispatch' }}
    runs-on: ubuntu-latest
    environment: production
    steps:
      - uses: aws-actions/configure-aws-credentials@v4
        with:
          role-to-arn: arn:aws:iam::ACCOUNT_ID:role/pyana-deploy
          aws-region: us-east-1
      - name: Deploy via SSM
        run: |
          aws ssm send-command \
            --instance-ids "${{ secrets.GATEWAY_INSTANCE_ID }}" \
            --document-name "AWS-RunShellScript" \
            --parameters 'commands=["cd /opt/pyana && docker compose -f docker-compose.prod.yml pull && docker compose -f docker-compose.prod.yml up -d"]' \
            --output text
```

Alternative (simpler, no SSM): use `appleboy/ssh-action` with deploy key stored in secrets.

---

## 5. Local Dev Workflow

### Updated `docker/docker-compose.yml` (local dev)

```yaml
version: '3.8'

services:
  node-0:
    build:
      context: ..
      dockerfile: docker/Dockerfile
    command: run --data-dir /data --bind 0.0.0.0 --port 8420 --gossip-port 9420
      --key-file node-0.key --morpheus --node-index 0 --federation-size 3
      --federation-peers node-1:9420,node-2:9420 --enable-pruning --enable-faucet
    volumes:
      - node0-data:/data
      - ./devnet-config/node-0.key:/data/node-0.key:ro
      - ./devnet-config/genesis.json:/data/genesis.json:ro
    ports:
      - "8420:8420"
      - "9420:9420"
    networks:
      - devnet
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8420/status"]
      interval: 5s
      timeout: 3s
      retries: 10

  node-1:
    # ... (same as current, add healthcheck)

  node-2:
    # ... (same as current, add healthcheck)

  gallery:
    build:
      context: ..
      dockerfile: docker/Dockerfile.multi
      args:
        PACKAGE: pyana-gallery
    command: --node-url http://node-0:8420 --listen 0.0.0.0:8430
    ports:
      - "8430:8430"
    depends_on:
      node-0:
        condition: service_healthy
    networks:
      - devnet

  bounty-board:
    build:
      context: ..
      dockerfile: docker/Dockerfile.multi
      args:
        PACKAGE: pyana-bounty-board
    command: --node-url http://node-0:8420 --listen 0.0.0.0:8440
    ports:
      - "8440:8440"
    depends_on:
      node-0:
        condition: service_healthy
    networks:
      - devnet

  compute-exchange:
    build:
      context: ..
      dockerfile: docker/Dockerfile.multi
      args:
        PACKAGE: compute-exchange
    command: --node-url http://node-0:8420 --listen 0.0.0.0:8450
    ports:
      - "8450:8450"
    depends_on:
      node-0:
        condition: service_healthy
    networks:
      - devnet

  explorer:
    image: nginx:alpine
    volumes:
      - ../site/explorer:/usr/share/nginx/html:ro
    ports:
      - "3000:80"
    networks:
      - devnet

  gallery-frontend:
    image: nginx:alpine
    volumes:
      - ../apps/gallery/frontend:/usr/share/nginx/html:ro
    ports:
      - "3001:80"
    networks:
      - devnet

volumes:
  node0-data:
  node1-data:
  node2-data:

networks:
  devnet:
    driver: bridge
```

### Hot-Reload for Development

For Rust development, Docker rebuilds are slow. Better approach:

1. **Nodes**: run directly via `scripts/test-devnet-cluster.sh` (already works)
2. **Apps**: `cargo watch -x 'run -p pyana-gallery -- --node-url http://127.0.0.1:8420 --listen 127.0.0.1:8430'`
3. **Frontend**: any static file server with watch (e.g., `python -m http.server` in `apps/gallery/frontend/`)
4. **Full stack (Docker)**: use for integration testing only, not daily dev

Add a `Makefile` or `justfile` target:

```makefile
devnet:
    scripts/test-devnet-cluster.sh

dev-gallery:
    cargo watch -x 'run -p pyana-gallery -- --node-url http://127.0.0.1:8420 --listen 127.0.0.1:8430'
```

### Integration Test Suite

Extend `scripts/test-devnet-cluster.sh` to also:
- Boot gallery against the running node
- Run HTTP-level tests (create gallery item, bid on auction, check state)
- Verify cross-node propagation of gallery state

Or create `tests/src/devnet_integration.rs` that programmatically spawns nodes and runs assertions.

---

## 6. Migration Steps (Ordered)

### Phase 1: Fix what's broken (no infra changes)

1. **Remove discovery.yml main push** — delete the "Check for changes on main" and "Commit and push discovery.json to main" steps. Discovery already correctly pushes to `federation-state` branch. This is a one-line PR.

2. **Update docker-compose.yml** — add healthchecks to nodes, add gallery/bounty-board/compute-exchange services. Test locally with `docker/start-devnet.sh`.

3. **Create `docker/Dockerfile.multi`** — parameterized Dockerfile that accepts `PACKAGE` build arg. Test that it builds all 4 targets locally for amd64.

### Phase 2: Multi-arch CI builds

4. **Add `.github/workflows/docker.yml`** — builds multi-arch images (amd64+arm64) and pushes to GHCR. Requires enabling GHCR packages on the repo and `packages: write` permission.

5. **Test ARM64 image** — pull from GHCR onto the Graviton instance, run manually to verify it works.

### Phase 3: AWS migration to Docker

6. **Install Docker on Graviton instance** — `curl -fsSL https://get.docker.com | sh` (or install docker via apt).

7. **Create `/opt/pyana/docker-compose.prod.yml`** — production compose file referencing GHCR images. Mount existing `/opt/pyana-data` into the node container.

8. **Migrate gateway from systemd to Docker Compose** — stop `pyana-gateway.service`, start Docker Compose. Caddy stays as systemd (or move it into compose too).

9. **Update Caddyfile** — add routes for gallery, bounty-board, compute-exchange.

10. **Update `deploy/aws/update.sh`** — change from `git pull && cargo build` to `docker compose pull && docker compose up -d`.

### Phase 4: CI-triggered deployment

11. **Create IAM role for deployment** — OIDC trust with GitHub Actions, permission to SSM or EC2 connect.

12. **Add `.github/workflows/deploy.yml`** — triggered on successful Docker build, deploys via SSM RunCommand or SSH.

13. **Add GitHub environment `production`** — with required reviewers if desired, secrets for instance ID.

### Phase 5: Monitoring

14. **Add Prometheus scraping** — either a lightweight Prometheus container in compose or push metrics to CloudWatch.

15. **Add structured logging** — ensure RUST_LOG includes JSON format for CloudWatch ingestion. Or add Vector/Fluent Bit sidecar.

16. **Alerting** — CloudWatch alarm on instance health, or simple uptime check via UptimeRobot/Healthchecks.io on `https://devnet.pyana.fg-goose.online/status`.

---

## 7. Dockerfile Update Needs

The current Dockerfile needs:

| Issue | Fix |
|-------|-----|
| Only builds `pyana-node` | Parameterize with `ARG PACKAGE` |
| No ARM64 awareness | Use `docker buildx` with QEMU or native ARM runners |
| No `.dockerignore` | Add one to exclude `target/`, `.git/`, `site/` from build context |
| `rust:latest` is unpinned | Pin to `rust:1.85` or match `rust-toolchain.toml` |
| No layer caching for deps | Add cargo-chef or split `Cargo.toml`/`Cargo.lock` copy for dep caching |
| No multi-binary final image | Consider single image with multiple binaries for simpler orchestration |

### Recommended `.dockerignore`

```
target/
.git/
site/
paper/
extension/
docs/
*.md
docker/devnet-config/
```

### Build Time Optimization

Cross-compiling Rust for ARM64 via QEMU on amd64 GHA runners is slow (~30-40min for this workspace). Options:
1. **ARM64 GHA runners** (GitHub now offers `ubuntu-latest-arm64`) — fastest, ~$0.005/min
2. **Cross-compilation with `cross`** — uses pre-built Docker images with cross-compilation toolchains
3. **Build on the Graviton instance itself** — fallback, keep `update.sh` as backup

**Recommendation:** Use ARM64 GHA runners for the arm64 build, standard runners for amd64. Split the matrix.

---

## 8. Cost Estimate

| Item | Monthly Cost |
|------|-------------|
| t4g.medium (reserved 1yr) | ~$15 |
| 30 GB gp3 EBS | ~$2.50 |
| Data transfer (low traffic devnet) | ~$1 |
| GHCR storage (< 1 GB) | Free |
| GHA minutes (existing) | Free tier |
| **Total** | **~$19/month** |

---

## Summary of Immediate Actions

1. Delete discovery-to-main push (5 min fix, high impact)
2. Write `docker/Dockerfile.multi` + `.dockerignore` (30 min)
3. Expand docker-compose with app services (30 min)
4. Add docker.yml workflow for multi-arch builds (1 hr)
5. Migrate Graviton instance from bare metal to Docker Compose (2 hr)
6. Add deployment workflow (1 hr)
