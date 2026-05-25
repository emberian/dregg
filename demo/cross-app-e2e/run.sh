#!/usr/bin/env bash
# cross-app-e2e — four-app composition demo.
#
# Walks the seven-step story:
#   alice issues credential → bob registers attested name → bob mounts
#   namespace → carol posts bounty → dan claims → dan fulfills → bob
#   consumes → carol settles.
#
# Each step produces a JSON receipt under state/; verify.py asserts
# every must_pass and must_not_pass entry in expected.json holds.
#
# Exit 0 iff every assertion passes.

set -u
set -o pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
STATE_DIR="$HERE/state"
LOG_DIR="$STATE_DIR/logs"
VENV_PY="$HERE/.venv/bin/python"

color_red()   { printf '\033[31m%s\033[0m' "$*"; }
color_green() { printf '\033[32m%s\033[0m' "$*"; }
color_dim()   { printf '\033[2m%s\033[0m' "$*"; }

step() { printf '\n[demo] step %s — %s\n' "$1" "$2"; }
ok()   { printf '       %s %s\n' "$(color_green ok)" "$*"; }
warn() { printf '       %s %s\n' "$(color_dim '~ ')" "$*"; }
fail() { printf '       %s %s\n' "$(color_red FAIL)" "$*"; }

reset_state() {
    rm -rf "$STATE_DIR"
    mkdir -p "$LOG_DIR"
}

ensure_venv() {
    if [ ! -x "$VENV_PY" ]; then
        echo "[demo] creating venv via uv…"
        if ! command -v uv >/dev/null; then
            fail "uv not found; install uv to bootstrap the demo venv"
            return 1
        fi
        ( cd "$HERE" && uv venv .venv ) >"$LOG_DIR/uv.venv.log" 2>&1 || true
        ( cd "$HERE" && uv pip install --python .venv/bin/python blake3 ) \
            >"$LOG_DIR/uv.pip.log" 2>&1 || {
            fail "uv pip install blake3 failed; see $LOG_DIR/uv.pip.log"
            return 1
        }
    fi
    if ! "$VENV_PY" -c "import blake3" >/dev/null 2>&1; then
        fail "blake3 not importable from $VENV_PY"
        return 1
    fi
    ok "venv ready ($VENV_PY)"
    return 0
}

run_step() {
    local label="$1"; shift
    local log="$LOG_DIR/$1.log"; shift
    if "$@" >"$log" 2>&1; then
        ok "$label"
        return 0
    fi
    fail "$label (see $log)"
    return 1
}

cd "$HERE"
reset_state

# ── Step 0: venv + deps ───────────────────────────────────────────────
step 0 "venv setup (uv + blake3)"
if ! ensure_venv; then
    exit 1
fi

PY="$VENV_PY"

# ── Step 1: bob identity (deterministic) ──────────────────────────────
step 1 "bob identity (deterministic seed → cell + pk hash)"
run_step "bob.py identity"   "01.bob.identity"   "$PY" "$HERE/bob.py"   identity --state-dir "$STATE_DIR" || exit 1
BOB_CELL=$("$PY" -c "import json,sys;print(json.load(open('$STATE_DIR/bob.identity.json'))['bob_cell'])")
ok "bob cell = ${BOB_CELL:0:16}…"

# ── Step 2: alice issues credential ───────────────────────────────────
step 2 "alice issues verified-developer-v1 credential to bob"
run_step "alice.py" "02.alice" "$PY" "$HERE/alice.py" --state-dir "$STATE_DIR" --bob-cell "$BOB_CELL" || exit 1

# ── Step 3: bob registers bob.dev in attested tier ────────────────────
step 3 "bob registers bob.dev in nameservice attested tier (CredentialSet)"
run_step "bob.py register" "03.bob.register" "$PY" "$HERE/bob.py" register --state-dir "$STATE_DIR" || exit 1

# ── Step 4: bob mounts namespace route ────────────────────────────────
step 4 "bob mounts pyana://bob.dev under governed-namespace"
run_step "bob.py mount" "04.bob.mount" "$PY" "$HERE/bob.py" mount --state-dir "$STATE_DIR" || exit 1

# ── Step 5: carol posts bounty + subscription ─────────────────────────
step 5 "carol posts bounty + creates subscription cell"
run_step "carol.py post"            "05a.carol.post"            "$PY" "$HERE/carol.py" post            --state-dir "$STATE_DIR" || exit 1
run_step "carol.py grant-consumer"  "05b.carol.grant_consumer"  "$PY" "$HERE/carol.py" grant-consumer  --state-dir "$STATE_DIR" || exit 1
run_step "carol.py grant-publisher" "05c.carol.grant_publisher" "$PY" "$HERE/carol.py" grant-publisher --state-dir "$STATE_DIR" || exit 1

# ── Step 6: dan claims ────────────────────────────────────────────────
step 6 "dan claims the bounty (Posted → Claimed publish)"
run_step "dan.py claim" "06.dan.claim" "$PY" "$HERE/dan.py" claim --state-dir "$STATE_DIR" || exit 1

# ── Step 7: dan fulfills ──────────────────────────────────────────────
step 7 "dan submits fulfillment (Claimed → Fulfilled publish)"
run_step "dan.py fulfill" "07.dan.fulfill" "$PY" "$HERE/dan.py" fulfill --state-dir "$STATE_DIR" || exit 1

# ── Step 8: bob consumes ──────────────────────────────────────────────
step 8 "bob consumes the subscription event"
run_step "bob.py consume" "08.bob.consume" "$PY" "$HERE/bob.py" consume --state-dir "$STATE_DIR" || exit 1

# ── Step 9: carol settles ─────────────────────────────────────────────
step 9 "carol settles after dispute window (Fulfilled → Settled publish)"
run_step "carol.py settle" "09.carol.settle" "$PY" "$HERE/carol.py" settle --state-dir "$STATE_DIR" || exit 1

# ── Step 10: verify ───────────────────────────────────────────────────
step 10 "verify all must_pass + must_not_pass entries in expected.json"
VERDICT="$STATE_DIR/verdict.json"
if "$PY" "$HERE/verify.py" \
        --state-dir "$STATE_DIR" \
        --expected  "$HERE/expected.json" \
        --out       "$VERDICT" \
        >"$LOG_DIR/10.verify.stdout" 2>"$LOG_DIR/10.verify.stderr"; then
    ok "every assertion passed"
    VERIFY_OK=1
else
    fail "some assertions failed (verdict at $VERDICT)"
    VERIFY_OK=0
fi

# ── Summary ───────────────────────────────────────────────────────────
echo
echo "[demo] ─── summary ──────────────────────────────────────────────"
if [ "$VERIFY_OK" = "1" ]; then
    printf '%s — cross-app composition story verified end-to-end\n' "$(color_green '[demo] PASS')"
    exit 0
else
    printf '%s — see logs in %s\n' "$(color_red '[demo] FAIL')" "$LOG_DIR"
    if [ -f "$VERDICT" ]; then
        echo
        "$PY" -c "
import json
v = json.load(open('$VERDICT'))
print('must_pass_failures:', v.get('must_pass_failures', []))
print('must_not_pass_failures:', v.get('must_not_pass_failures', []))
"
    fi
    exit 1
fi
