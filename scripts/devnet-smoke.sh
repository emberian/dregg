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
TRIGGER_ACTION=1
EXPECT_WITNESS=0
SMOKE_AGENT="${DREGG_SMOKE_AGENT:-0000000000000000000000000000000000000000000000000000000000000000}"
SMOKE_NONCE="${DREGG_SMOKE_NONCE:-}"
SMOKE_FEE="${DREGG_SMOKE_FEE:-100}"
SUBMIT_TURN_HASH=""
SUBMIT_PROOF_STATUS=""
SUBMIT_HAS_WITNESS=""
SUBMIT_WITNESS_COUNT=""

usage() {
  cat <<'EOF'
Usage: scripts/devnet-smoke.sh [options]

Builds the local node and static site, then probes a devnet node API used by
Starbridge and Explorer. By default it also submits one deterministic HTTP turn
through the same node API surface used by bot/devnet clients, then verifies that
the resulting receipt is explorer-visible.

Options:
  --node-url URL      Node API base URL (default: http://127.0.0.1:8420)
  --site-url URL      Static site URL to probe/open, usually http://127.0.0.1:3000
  --skip-build        Do not build node or site
  --skip-node-build   Do not build dregg-node
  --skip-site-build   Do not build site/dist
  --release           Build dregg-node with cargo --release
  --no-trigger        Only probe; do not submit a smoke turn
  --expect-witness    Require the submitted turn to produce persisted witness material
  --agent HEX         Hex cell id accepted by /api/turns/submit (node derives signer cell)
  --nonce N           Nonce for the smoke turn (default: unix timestamp)
  --fee N             Fee for the smoke turn (default: 100)
  --open              Open Starbridge and Explorer URLs after probes
  --non-strict        Report probe failures but exit 0
  -h, --help          Show this help

Environment:
  DREGG_NODE_URL      Same as --node-url
  DREGG_SITE_URL      Same as --site-url
  DREGG_SMOKE_AGENT   Same as --agent
  DREGG_SMOKE_NONCE   Same as --nonce

Notes:
  This harness uses /api/turns/submit as a deterministic local substitute for a
  Discord slash command. The live Discord step is: run dregg-discord-bot against
  the same DREGG_NODE_URL and invoke a command that calls DevnetClient
  submit_app_action/submit_transfer; then rerun this script with --no-trigger to
  verify the explorer-visible receipt/event surface.
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
    --no-trigger)
      TRIGGER_ACTION=0
      shift
      ;;
    --expect-witness)
      EXPECT_WITNESS=1
      shift
      ;;
    --agent)
      SMOKE_AGENT="${2:?missing hex cell id for --agent}"
      shift 2
      ;;
    --nonce)
      SMOKE_NONCE="${2:?missing nonce for --nonce}"
      shift 2
      ;;
    --fee)
      SMOKE_FEE="${2:?missing fee for --fee}"
      shift 2
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

json_field() {
  local field="$1"
  node -e '
const field = process.argv[1];
const input = require("fs").readFileSync(0, "utf8");
const value = JSON.parse(input);
const out = value == null ? undefined : value[field];
if (out === undefined || out === null) process.exit(2);
if (typeof out === "object") console.log(JSON.stringify(out));
else console.log(String(out));
' "$field"
}

http_body_json() {
  local path="$1"
  local url="${NODE_URL%/}${path}"
  local code
  local tmp

  tmp="$(mktemp)"
  code="$(curl -sS --connect-timeout 2 --max-time 12 -H 'Accept: application/json' -o "$tmp" -w '%{http_code}' "$url" 2>/dev/null || true)"
  if [ "$code" != "200" ]; then
    rm -f "$tmp"
    printf 'HTTP %s' "${code:-000}"
    return 1
  fi
  if ! json_valid < "$tmp"; then
    rm -f "$tmp"
    printf 'non-JSON'
    return 1
  fi
  cat "$tmp"
  rm -f "$tmp"
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

submit_smoke_turn() {
  local nonce="$SMOKE_NONCE"
  local body
  local tmp
  local code
  local url="${NODE_URL%/}/api/turns/submit"

  if [ -z "$nonce" ]; then
    nonce="$(date +%s)"
  fi

  body="$(node -e '
const agent = process.argv[1];
const nonce = Number(process.argv[2]);
const fee = Number(process.argv[3]);
console.log(JSON.stringify({
  agent,
  nonce,
  fee,
  memo: `devnet-smoke:http-turn:${nonce}`
}));
' "$SMOKE_AGENT" "$nonce" "$SMOKE_FEE")"

  tmp="$(mktemp)"
  code="$(curl -sS --connect-timeout 2 --max-time 30 \
    -H 'Accept: application/json' \
    -H 'Content-Type: application/json' \
    -o "$tmp" \
    -w '%{http_code}' \
    -d "$body" \
    "$url" 2>/dev/null || true)"

  if [ "$code" != "200" ]; then
    fail "HTTP smoke turn submit returned HTTP ${code:-000}"
    rm -f "$tmp"
    return 1
  fi
  if ! json_valid < "$tmp"; then
    fail "HTTP smoke turn submit returned non-JSON"
    rm -f "$tmp"
    return 1
  fi

  local accepted
  accepted="$(json_field accepted < "$tmp" 2>/dev/null || true)"
  SUBMIT_TURN_HASH="$(json_field turn_hash < "$tmp" 2>/dev/null || true)"
  SUBMIT_PROOF_STATUS="$(json_field proof_status < "$tmp" 2>/dev/null || true)"
  SUBMIT_HAS_WITNESS="$(json_field has_witness < "$tmp" 2>/dev/null || true)"
  SUBMIT_WITNESS_COUNT="$(json_field witness_count < "$tmp" 2>/dev/null || true)"

  if [ "$accepted" != "true" ]; then
    fail "HTTP smoke turn rejected: $(cat "$tmp")"
    rm -f "$tmp"
    return 1
  fi

  rm -f "$tmp"
  pass "HTTP smoke turn accepted (${SUBMIT_TURN_HASH:-unknown})"

  case "$SUBMIT_PROOF_STATUS" in
    proved|Proved|not_required|NotRequired)
      pass "submit response proof_status=$SUBMIT_PROOF_STATUS"
      ;;
    *)
      fail "submit response has unexpected proof_status=$SUBMIT_PROOF_STATUS"
      ;;
  esac

  if [ "$EXPECT_WITNESS" -eq 1 ]; then
    if [ "$SUBMIT_HAS_WITNESS" = "true" ] && [ "${SUBMIT_WITNESS_COUNT:-0}" -gt 0 ]; then
      pass "submit response reports persisted witness_count=$SUBMIT_WITNESS_COUNT"
    else
      fail "submit response did not report persisted witness material"
    fi
  elif [ "$SUBMIT_HAS_WITNESS" = "true" ]; then
    pass "submit response reports persisted witness_count=${SUBMIT_WITNESS_COUNT:-unknown}"
  else
    warn "submitted HTTP turn has no witness material; use --expect-witness for proof-producing lanes"
  fi
}

assert_receipt_visible() {
  if [ -z "$SUBMIT_TURN_HASH" ]; then
    warn "no submitted turn hash; skipping receipt/event assertions"
    return 0
  fi

  local receipts
  if receipts="$(http_body_json "/api/receipts")"; then
    if printf '%s' "$receipts" | TURN_HASH="$SUBMIT_TURN_HASH" node -e '
const turnHash = process.env.TURN_HASH.toLowerCase();
const receipts = JSON.parse(require("fs").readFileSync(0, "utf8"));
if (!Array.isArray(receipts)) process.exit(2);
const found = receipts.find((r) => String(r.turn_hash || "").toLowerCase() === turnHash);
if (!found) process.exit(1);
console.log(found.receipt_hash || found.hash || "");
' >/tmp/dregg-smoke-receipt.$$; then
      local receipt_hash
      receipt_hash="$(cat /tmp/dregg-smoke-receipt.$$)"
      rm -f /tmp/dregg-smoke-receipt.$$
      pass "submitted turn is visible in /api/receipts"
      if [ -n "$receipt_hash" ]; then
        assert_witness_endpoint "$receipt_hash"
      fi
    else
      rm -f /tmp/dregg-smoke-receipt.$$
      fail "submitted turn ${SUBMIT_TURN_HASH} not found in /api/receipts"
    fi
  else
    fail "/api/receipts unavailable after submit"
  fi

  local events
  if events="$(http_body_json "/api/events")"; then
    if printf '%s' "$events" | TURN_HASH="$SUBMIT_TURN_HASH" node -e '
const turnHash = process.env.TURN_HASH.toLowerCase();
const events = JSON.parse(require("fs").readFileSync(0, "utf8"));
if (!Array.isArray(events)) process.exit(2);
process.exit(events.some((e) => String(e.turn_hash || "").toLowerCase() === turnHash) ? 0 : 1);
'; then
      pass "submitted turn is visible in /api/events"
    else
      fail "submitted turn ${SUBMIT_TURN_HASH} not found in /api/events"
    fi
  else
    fail "/api/events unavailable after submit"
  fi
}

assert_witness_endpoint() {
  local receipt_hash="$1"
  local witnesses
  if witnesses="$(http_body_json "/api/receipts/${receipt_hash}/witnesses")"; then
    if printf '%s' "$witnesses" | EXPECT_WITNESS="$EXPECT_WITNESS" node -e '
const expectWitness = process.env.EXPECT_WITNESS === "1";
const value = JSON.parse(require("fs").readFileSync(0, "utf8"));
const list = Array.isArray(value) ? value : (Array.isArray(value.witnessed_receipts) ? value.witnessed_receipts : []);
if (expectWitness && list.length === 0) process.exit(1);
process.exit(0);
'; then
      pass "receipt witness endpoint is queryable"
    else
      fail "receipt witness endpoint has no witness artifact for ${receipt_hash}"
    fi
  else
    fail "receipt witness endpoint unavailable for ${receipt_hash}"
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
http_get_json "/api/events" "events list" || true
http_get_first_json "receipts list" "/api/starbridge/receipts?limit=100" "/api/receipts" "/api/receipts/recent" || true
http_get_first_json "blocks list" "/api/blocks" "/federation/roots" "/checkpoint/latest" || true

if [ "$TRIGGER_ACTION" -eq 1 ]; then
  log "=== Triggering deterministic HTTP turn ==="
  submit_smoke_turn || true
  assert_receipt_visible || true
else
  warn "skipped HTTP turn trigger"
fi

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
