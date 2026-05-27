#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
NODE_URL="${DREGG_NODE_URL:-http://127.0.0.1:8420}"
SITE_URL="${DREGG_SITE_URL:-}"
BUILD_NODE=1
BUILD_SITE=1
OPEN_URLS=0
RELEASE=0
STRICT=1

usage() {
  cat <<'EOF'
Usage: scripts/devnet-smoke.sh [options]

Builds the local node and static site, then probes a devnet node API used by
Starbridge and Explorer.

Options:
  --node-url URL      Node API base URL (default: http://127.0.0.1:8420)
  --site-url URL      Static site URL to probe/open, usually http://127.0.0.1:3000
  --skip-build        Do not build node or site
  --skip-node-build   Do not build dregg-node
  --skip-site-build   Do not build site/dist
  --release           Build dregg-node with cargo --release
  --open              Open Starbridge and Explorer URLs after probes
  --non-strict        Report probe failures but exit 0
  -h, --help          Show this help

Environment:
  DREGG_NODE_URL      Same as --node-url
  DREGG_SITE_URL      Same as --site-url
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --node-url)
      NODE_URL="${2:?missing URL for --node-url}"
      shift 2
      ;;
    --site-url)
      SITE_URL="${2:?missing URL for --site-url}"
      shift 2
      ;;
    --skip-build)
      BUILD_NODE=0
      BUILD_SITE=0
      shift
      ;;
    --skip-node-build)
      BUILD_NODE=0
      shift
      ;;
    --skip-site-build)
      BUILD_SITE=0
      shift
      ;;
    --release)
      RELEASE=1
      shift
      ;;
    --open)
      OPEN_URLS=1
      shift
      ;;
    --non-strict)
      STRICT=0
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

PASS=0
FAIL=0
WARN=0

log() {
  printf '%s\n' "$*"
}

pass() {
  PASS=$((PASS + 1))
  printf 'ok   %s\n' "$*"
}

warn() {
  WARN=$((WARN + 1))
  printf 'warn %s\n' "$*"
}

fail() {
  FAIL=$((FAIL + 1))
  printf 'fail %s\n' "$*"
}

run_required() {
  local label="$1"
  shift

  if "$@"; then
    pass "$label"
    return 0
  fi

  fail "$label"
  if [ "$STRICT" -eq 1 ]; then
    exit 1
  fi

  return 1
}

json_valid() {
  node -e 'JSON.parse(require("fs").readFileSync(0, "utf8"))' >/dev/null 2>&1
}

http_probe_json() {
  local path="$1"
  local url="${NODE_URL%/}${path}"
  local body
  local code
  local tmp

  tmp="$(mktemp)"
  code="$(curl -sS --connect-timeout 2 --max-time 8 -H 'Accept: application/json' -o "$tmp" -w '%{http_code}' "$url" 2>/dev/null || true)"
  body="$(cat "$tmp")"
  rm -f "$tmp"

  if [ "$code" != "200" ]; then
    printf 'HTTP %s' "${code:-000}"
    return 1
  fi

  if ! printf '%s' "$body" | json_valid; then
    printf 'non-JSON'
    return 1
  fi

  printf 'ok'
  return 0
}

http_get_json() {
  local path="$1"
  local label="$2"
  local result

  if result="$(http_probe_json "$path")"; then
    pass "$label ($path)"
    return 0
  fi

  fail "$label ($path) returned $result"
  return 1
}

http_get_first_json() {
  local label="$1"
  shift
  local path
  local result
  local failures=""

  for path in "$@"; do
    if result="$(http_probe_json "$path")"; then
      pass "$label ($path)"
      return 0
    fi
    failures="${failures}${failures:+; }${path}: ${result}"
  done

  fail "$label had no working endpoint ($failures)"
  return 1
}

site_get() {
  local path="$1"
  local label="$2"
  local url="${SITE_URL%/}${path}"
  local code

  code="$(curl -sS --connect-timeout 2 --max-time 8 -o /dev/null -w '%{http_code}' "$url" 2>/dev/null || true)"
  if [ "$code" = "200" ]; then
    pass "$label ($path)"
  else
    fail "$label ($path) returned HTTP ${code:-000}"
  fi
}

open_url() {
  local url="$1"
  if command -v open >/dev/null 2>&1; then
    open "$url"
  elif command -v xdg-open >/dev/null 2>&1; then
    xdg-open "$url" >/dev/null 2>&1 &
  else
    warn "no opener found for $url"
  fi
}

log "=== Devnet smoke ==="
log "repo:     $ROOT"
log "node url: $NODE_URL"
if [ -n "$SITE_URL" ]; then
  log "site url: $SITE_URL"
fi
log ""

if [ "$BUILD_NODE" -eq 1 ]; then
  if [ "$RELEASE" -eq 1 ]; then
    log "=== Building node (release) ==="
    run_required "dregg-node build" bash -c "cd '$ROOT' && cargo build --release -p dregg-node" || true
  else
    log "=== Building node ==="
    run_required "dregg-node build" bash -c "cd '$ROOT' && cargo build -p dregg-node" || true
  fi
else
  warn "skipped dregg-node build"
fi

if [ "$BUILD_SITE" -eq 1 ]; then
  log "=== Building static site ==="
  run_required "site build" bash -c "cd '$ROOT/site' && npm run build" || true
else
  warn "skipped site build"
fi

if [ -f "$ROOT/site/dist/explorer/index.html" ]; then
  pass "Explorer artifact exists"
else
  fail "Explorer artifact missing at site/dist/explorer/index.html"
fi

if [ -f "$ROOT/site/dist/starbridge.html" ] || [ -f "$ROOT/site/dist/starbridge/index.html" ]; then
  pass "Starbridge artifact exists"
else
  fail "Starbridge artifact missing in site/dist"
fi

log "=== Probing node API ==="
http_get_json "/status" "node status" || true
http_get_json "/api/cells" "cells list" || true
http_get_first_json "receipts list" "/api/starbridge/receipts?limit=100" "/api/receipts" "/api/receipts/recent" || true
http_get_first_json "blocks list" "/api/blocks" "/federation/roots" "/checkpoint/latest" || true

if [ -n "$SITE_URL" ]; then
  log "=== Probing static site ==="
  site_get "/" "site root"
  site_get "/explorer/" "Explorer page"
  site_get "/starbridge.html" "Starbridge page"
fi

if [ "$OPEN_URLS" -eq 1 ]; then
  log "=== Opening URLs ==="
  if [ -n "$SITE_URL" ]; then
    open_url "${SITE_URL%/}/starbridge.html"
    open_url "${SITE_URL%/}/explorer/"
  else
    open_url "file://$ROOT/site/dist/starbridge.html"
    open_url "file://$ROOT/site/dist/explorer/index.html"
  fi
fi

log ""
log "=== Results ==="
log "passed: $PASS"
log "warned: $WARN"
log "failed: $FAIL"

if [ "$FAIL" -gt 0 ] && [ "$STRICT" -eq 1 ]; then
  log "Smoke failed. Start a devnet node or pass --node-url for live API probes."
  exit 1
fi

exit 0
