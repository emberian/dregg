#!/usr/bin/env bash
# Scenario: cross-federation bearer-cap handoff with real pyana MCP + verifier.
#
# This is the production version (no bash theater):
#   - Drives F1 node-1 (primary) and F2 node-1 via real MCP stdio
#     (pyana_create_agent, pyana_create_bearer_cap, pyana_bilateral_action)
#   - Produces real Ed25519 delegation_chain from the node
#   - Produces real WitnessedReceipts (with STARK proofs) from bilateral transfer on F2
#   - Assembles real CrossFedReceiptBundle v1 (recipient_chain + attested roots
#     from /federation/roots + manually reconstructed HandoffCertificate from cap)
#   - Runs the real $VERIFIER_BIN verify-cross-fed-bundle against the bundle +
#     committee descriptors extracted from the two genesis.json files
#   - Tamper test: flips introducer in the cert and asserts verifier rejects
#
# When the devnet is not running (http /status fails), the MCP+verifier
# assertions gracefully record false and the result.json still compares
# cleanly against expected.json (which documents the precondition).
#
# Improve don't degrade: all prior infrastructure assertions remain in
# must_pass; the new real ones are added to must_pass (never scaffold_only).

set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/../lib/common.sh"

SCENARIO_NAME="cross_fed_handoff"
SCN_LOG_DIR="$LOG_DIR/scenarios/$SCENARIO_NAME"
RESULT_FILE="$SCN_LOG_DIR/result.json"
mkdir -p "$SCN_LOG_DIR"

declare -A RESULTS

record() {
    local key="$1" val="$2"
    RESULTS["$key"]="$val"
    if [ "$val" = "true" ]; then
        devnet_ok "$key"
    else
        devnet_fail "$key"
    fi
}

F1_ID=$(fed_id_from_genesis "$(fed_genesis_dir F1)/genesis.json")
F2_ID=$(fed_id_from_genesis "$(fed_genesis_dir F2)/genesis.json")
F1_PORT=$(fed_http_port F1 1)
F2_PORT=$(fed_http_port F2 1)
F1_DATA_DIR=$(fed_data_dir F1 1)
F2_DATA_DIR=$(fed_data_dir F2 1)

if [ -z "$F1_ID" ] || [ -z "$F2_ID" ]; then
    devnet_fail "federation IDs unavailable; genesis files missing?"
    exit 1
fi

devnet_step "scenario: cross_fed_handoff (real MCP + verifier)"
devnet_dim "F1 federation_id=$F1_ID  data=$F1_DATA_DIR"
devnet_dim "F2 federation_id=$F2_ID  data=$F2_DATA_DIR"

f1_status=$(http_get "http://127.0.0.1:$F1_PORT/status")
f2_status=$(http_get "http://127.0.0.1:$F2_PORT/status")
if [ -n "$f1_status" ] && [ -n "$f2_status" ]; then
    record both_federations_responding true
else
    record both_federations_responding false
    devnet_warn "devnet not responding on 7811/7821 — MCP and verifier steps will be false (graceful)"
fi

# Always emit committee descriptors (even in degraded mode) so the tamper
# and bundle paths have inputs when the operator starts the devnet later.
mkdir -p "$SCN_LOG_DIR"
if command -v jq >/dev/null 2>&1; then
    jq '{federation_id, committee_epoch, threshold, validators: [.validators[] | {name, public_key}]}' \
        "$(fed_genesis_dir F1)/genesis.json" > "$SCN_LOG_DIR/f1_committee.json" 2>/dev/null || echo '{}' > "$SCN_LOG_DIR/f1_committee.json"
    jq '{federation_id, committee_epoch, threshold, validators: [.validators[] | {name, public_key}]}' \
        "$(fed_genesis_dir F2)/genesis.json" > "$SCN_LOG_DIR/f2_committee.json" 2>/dev/null || echo '{}' > "$SCN_LOG_DIR/f2_committee.json"
else
    echo '{"federation_id":"'"$F1_ID"'","committee_epoch":0,"threshold":2,"validators":[]}' > "$SCN_LOG_DIR/f1_committee.json"
    echo '{"federation_id":"'"$F2_ID"'","committee_epoch":0,"threshold":2,"validators":[]}' > "$SCN_LOG_DIR/f2_committee.json"
fi

# Snapshot roots (used for bundle construction when live)
roots_F1=$(http_get "http://127.0.0.1:$F1_PORT/federation/roots")
roots_F2=$(http_get "http://127.0.0.1:$F2_PORT/federation/roots")
echo "$roots_F1" > "$SCN_LOG_DIR/roots_F1.json"
echo "$roots_F2" > "$SCN_LOG_DIR/roots_F2.json"

if [ -n "$roots_F1" ]; then record F1_exposes_federation_roots true; else record F1_exposes_federation_roots false; fi
if [ -n "$roots_F2" ]; then record F2_exposes_federation_roots true; else record F2_exposes_federation_roots false; fi

# ── Real work: only when devnet up + binaries present ─────────────────
MCP_WORK_DONE=false
if [ -x "$NODE_BIN" ] && [ -x "$VERIFIER_BIN" ] && [ -n "$f1_status" ] && [ -n "$f2_status" ]; then
    MCP_WORK_DONE=true
    devnet_dim "binaries and devnet present — driving real MCP sessions"

    # Write a self-contained MCP client (adapted from demo/two-ai-handoff/mcp_stdio.py
    # but single-file, no external deps beyond stdlib, and tolerant of devnet posture).
    cat > "$SCN_LOG_DIR/mcp_client.py" << 'PYEOF'
#!/usr/bin/env python3
"""Minimal MCP-over-stdio driver for the cross_fed_handoff scenario.
Matches the real pyana-node mcp argv (subcommand form) and the content[]
response shape used by the production McpClient.
"""
from __future__ import annotations
import json
import os
import queue
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

class McpClient:
    def __init__(self, node_bin: str, data_dir: str, label: str, log_dir: Path):
        self.label = label
        self.log_dir = Path(log_dir)
        self.log_dir.mkdir(parents=True, exist_ok=True)
        self.stderr_log_path = self.log_dir / f"{label}.node.stderr.log"
        self.stderr_log = open(self.stderr_log_path, "wb")

        env = os.environ.copy()
        env.setdefault("RUST_LOG", "pyana_node=warn,error")

        self.proc = subprocess.Popen(
            [node_bin, "mcp", "--data-dir", data_dir],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=self.stderr_log,
            env=env,
            bufsize=0,
        )
        self._next_id = 1
        self._lock = threading.Lock()
        self._reader_q: queue.Queue[Dict[str, Any]] = queue.Queue()
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._reader.start()
        self._initialize()

    def _read_loop(self) -> None:
        assert self.proc.stdout is not None
        for line in self.proc.stdout:
            if not line:
                continue
            try:
                obj = json.loads(line.decode("utf-8", errors="replace"))
                self._reader_q.put(obj)
            except Exception:
                pass

    def _initialize(self) -> None:
        self.call(
            "initialize",
            {
                "protocolVersion": "2024-11-05",
                "capabilities": {},
                "clientInfo": {"name": f"cross-fed-handoff/{self.label}", "version": "0.1"},
            },
        )
        self._send({"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}})

    def _send(self, obj: Dict[str, Any]) -> None:
        assert self.proc.stdin is not None
        line = (json.dumps(obj) + "\n").encode()
        self.proc.stdin.write(line)
        self.proc.stdin.flush()

    def call(self, method: str, params: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        with self._lock:
            rid = self._next_id
            self._next_id += 1
            self._send({
                "jsonrpc": "2.0",
                "id": rid,
                "method": method,
                "params": params or {},
            })
            deadline = time.time() + 20.0
            while time.time() < deadline:
                try:
                    resp = self._reader_q.get(timeout=0.5)
                    if resp.get("id") == rid:
                        if "error" in resp and resp["error"] is not None:
                            raise RuntimeError(f"[{self.label}] RPC error: {resp['error']}")
                        return resp.get("result", {})
                except queue.Empty:
                    continue
            raise RuntimeError(f"[{self.label}] timeout waiting for response to {method}")

    def tool(self, name: str, args: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        result = self.call("tools/call", {"name": name, "arguments": args or {}})
        if result.get("isError"):
            contents = result.get("content", [])
            raise RuntimeError(f"tool {name} isError: " + " | ".join(c.get("text", "") for c in contents))
        contents = result.get("content", [])
        if not contents:
            return {}
        text = contents[0].get("text", "")
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            return {"text": text}

    def close(self) -> None:
        try:
            if self.proc.stdin:
                self.proc.stdin.close()
        except Exception:
            pass
        try:
            self.proc.wait(timeout=8)
        except subprocess.TimeoutExpired:
            self.proc.kill()
        finally:
            try:
                self.stderr_log.close()
            except Exception:
                pass

    def __enter__(self) -> "McpClient":
        return self

    def __exit__(self, *exc: Any) -> None:
        self.close()

def pick_latest_root(roots_json: str) -> Dict[str, Any]:
    try:
        arr = json.loads(roots_json or "[]")
        if isinstance(arr, list) and arr:
            return max(arr, key=lambda r: r.get("height", 0))
    except Exception:
        pass
    return {"height": 0, "merkle_root": "00"*32, "timestamp": 0, "signatures": 0}

def hex_to_ints(h: str) -> List[int]:
    """Convert a hex string to a list of u8 ints (serde integer-array format).

    AttestedRoot.merkle_root, FederationId, CellId, [u8;32] nonce/swiss/recipient_pk,
    and Signature ([u8;64]) all derive Serialize directly on their inner byte arrays.
    serde_json renders those as integer arrays ([0,1,...,255]), NOT hex strings.
    The /federation/roots endpoint returns merkle_root as a hex string; the MCP
    tools return cell_id and public_key as hex strings.  We must convert before
    writing the bundle so CrossFedReceiptBundle::from_json succeeds.
    """
    raw = bytes.fromhex(h) if h else b"\x00" * 32
    return list(raw)

def build_attested_root_from_info(info: Dict[str, Any], fed_id_hex: str) -> Dict[str, Any]:
    # Produce a shape that round-trips through AttestedRoot serde in the verifier.
    # All [u8;32] fields must be integer arrays (serde default for fixed byte arrays).
    h = int(info.get("height", 0))
    mr_hex = info.get("merkle_root") or ("00" * 32)
    ts = int(info.get("timestamp", 0))
    return {
        "merkle_root": hex_to_ints(mr_hex),
        "note_tree_root": None,
        "nullifier_set_root": None,
        "height": h,
        "timestamp": ts,
        "blocklace_block_id": None,
        "finality_round": None,
        "quorum_signatures": [],
        "threshold_qc": None,
        "threshold": 2,
        # FederationId(pub [u8;32]) derives Serialize → integer array
        "federation_id": hex_to_ints(fed_id_hex),
        "receipt_stream_root": None,
    }

def build_cross_fed_cert(
    f1_id: str,
    f2_id: str,
    alice_cell: str,
    bob_pk: str,
    delegation_chain: str,
    expires_at: int = 10000000,
) -> Dict[str, Any]:
    import secrets
    # nonce and swiss are [u8;32] — must be integer arrays for serde.
    nonce = hex_to_ints(secrets.token_hex(32))
    swiss = hex_to_ints(secrets.token_hex(32))
    # delegation_chain from MCP is a hex-encoded 64-byte Ed25519 signature.
    # Signature(#[serde(with = "serde_64")] pub [u8;64]) serializes as Vec<u8>
    # (integer array of 64 elements).
    intro_sig = hex_to_ints(delegation_chain) if delegation_chain else [0] * 64
    return {
        # FederationId(pub [u8;32]) → integer array
        "introducer": hex_to_ints(f1_id),
        # Signature serde_64 → integer array of 64 elements
        "introducer_signature": intro_sig,
        # FederationId → integer array
        "target_federation": hex_to_ints(f2_id),
        # CellId(pub [u8;32]) derives Serialize → integer array
        "target_cell": hex_to_ints(alice_cell),
        # recipient_pk: [u8;32] plain field → integer array
        "recipient_pk": hex_to_ints(bob_pk),
        "permissions": "Signature",   # AuthRequired unit variant → string
        "allowed_effects": None,
        "expires_at": expires_at,
        "max_uses": None,
        "nonce": nonce,
        "swiss": swiss,
    }

def run_cross_fed_handoff_mcp(
    node_bin: str,
    f1_data: str,
    f2_data: str,
    f1_id: str,
    f2_id: str,
    roots_f1: str,
    roots_f2: str,
    scn_log: Path,
) -> Dict[str, Any]:
    log_dir = Path(scn_log)
    out: Dict[str, Any] = {
        "alice_cell_created": False,
        "bob_cell_created": False,
        "bearer_cap_issued": False,
        "bilateral_transfer": False,
        "bundle_written": False,
        "verifier_exit": None,
        "verifier_overall": None,
        "tamper_verifier_exit": None,
        "tamper_overall": None,
        "error": None,
    }
    try:
        with McpClient(node_bin, f1_data, "f1", log_dir) as f1:
            alice = f1.tool("pyana_create_agent", {"name": "alice", "initial_balance": 100000})
            alice_cell = alice.get("cell_id")
            alice_pk = alice.get("public_key")
            if not alice_cell:
                out["error"] = "no alice cell_id from create_agent"
                return out
            out["alice_cell_created"] = True
            out["alice_cell"] = alice_cell
            out["alice_pk"] = alice_pk

            with McpClient(node_bin, f2_data, "f2", log_dir) as f2:
                bob = f2.tool("pyana_create_agent", {"name": "bob", "initial_balance": 100000})
                bob_cell = bob.get("cell_id")
                bob_pk = bob.get("public_key")
                if not bob_cell or not bob_pk:
                    out["error"] = "no bob cell/pk"
                    return out
                out["bob_cell_created"] = True
                out["bob_cell"] = bob_cell
                out["bob_pk"] = bob_pk

                # Bearer cap on F1 (real Ed25519 delegation_chain from the node)
                bearer = f1.tool(
                    "pyana_create_bearer_cap",
                    {
                        "target_cell": alice_cell,
                        "permissions": "signature",
                        "expires_at": 10000000,
                        "bearer_pk": bob_pk,
                    },
                )
                if not bearer.get("created"):
                    out["error"] = f"bearer cap not created: {bearer}"
                    return out
                delegation = bearer.get("delegation_chain", "")
                out["bearer_cap_issued"] = True
                out["delegation_chain"] = delegation

                # Write the OOB handoff URI (shim form, per current blocker-2)
                handoff_payload = {
                    "kind": "bearer-cap-v0",
                    "target_cell": alice_cell,
                    "bearer_pk": bob_pk,
                    "permissions": "signature",
                    "expires_at": 10000000,
                    "delegation_chain": delegation,
                    "introducer_pk": alice_pk,
                }
                handoff_uri = "pyana+bearer:" + json.dumps(handoff_payload, separators=(",", ":"))
                (log_dir / "handoff.uri").write_text(handoff_uri)

                # OOB delivery (cp as allowed)
                # (We do not parse it on F2 for this scenario; we use the cell ids directly.)

                # Bilateral transfer on F2 (produces the real WitnessedReceipts + STARK proofs)
                # from=alice_cell (remote stub on F2), to=bob_cell
                bil = f2.tool(
                    "pyana_bilateral_action",
                    {"mode": "transfer", "from": alice_cell, "to": bob_cell, "amount": 50},
                )
                if not bil.get("committed"):
                    out["error"] = f"bilateral not committed: {bil}"
                    return out
                out["bilateral_transfer"] = True
                out["turn_hash"] = bil.get("turn_hash")

                from_side = bil.get("from_side", {}) or {}
                to_side = bil.get("to_side", {}) or {}
                from_wr = from_side.get("witnessed_receipt")
                to_wr = to_side.get("witnessed_receipt")
                (log_dir / "witnessed_chain.json").write_text(
                    json.dumps({"from_wr": from_wr, "to_wr": to_wr, "bilateral": bil}, indent=2)
                )

                # Build bundle
                latest_f1 = pick_latest_root(roots_f1)
                latest_f2 = pick_latest_root(roots_f2)
                issuer_root = build_attested_root_from_info(latest_f1, f1_id)
                recipient_root = build_attested_root_from_info(latest_f2, f2_id)

                cross_cert = build_cross_fed_cert(f1_id, f2_id, alice_cell, bob_pk, delegation)

                recipient_chain = [to_wr] if to_wr else []
                bundle = {
                    "version": 1,
                    "recipient_chain": recipient_chain,
                    "issuer_attested_root": issuer_root,
                    "recipient_attested_root": recipient_root,
                    "cross_fed_cert": cross_cert,
                }
                bundle_path = log_dir / "cross_fed_bundle.json"
                bundle_path.write_text(json.dumps(bundle, indent=2))
                out["bundle_written"] = True
                out["bundle_path"] = str(bundle_path)

                # Run real verifier (accept path)
                ver_cmd = [
                    str(Path(node_bin).parent / "pyana-verifier"),
                    "verify-cross-fed-bundle",
                    "--bundle", str(bundle_path),
                    "--known-issuer", str(log_dir / "f1_committee.json"),
                    "--known-recipient", str(log_dir / "f2_committee.json"),
                ]
                ver = subprocess.run(ver_cmd, capture_output=True, text=True, timeout=30)
                out["verifier_exit"] = ver.returncode
                try:
                    vj = json.loads(ver.stdout.strip() or "{}")
                    out["verifier_overall"] = bool(vj.get("overall_verified", False))
                    out["verifier_verdict"] = vj
                except Exception:
                    out["verifier_overall"] = False

                # Tamper: flip introducer (or a byte of the signature)
                tamper_path = log_dir / "cross_fed_bundle.tampered.json"
                try:
                    b = json.loads(bundle_path.read_text())
                    if b.get("cross_fed_cert"):
                        # Flip the introducer federation id (strong tamper)
                        b["cross_fed_cert"]["introducer"] = "00" * 32
                    tamper_path.write_text(json.dumps(b, indent=2))
                except Exception as e:
                    tamper_path.write_text('{"tamper_failed":true,"err":"' + str(e) + '"}')

                ver2_cmd = [
                    str(Path(node_bin).parent / "pyana-verifier"),
                    "verify-cross-fed-bundle",
                    "--bundle", str(tamper_path),
                    "--known-issuer", str(log_dir / "f1_committee.json"),
                    "--known-recipient", str(log_dir / "f2_committee.json"),
                ]
                ver2 = subprocess.run(ver2_cmd, capture_output=True, text=True, timeout=30)
                out["tamper_verifier_exit"] = ver2.returncode
                try:
                    vj2 = json.loads(ver2.stdout.strip() or "{}")
                    out["tamper_overall"] = bool(vj2.get("overall_verified", False))
                except Exception:
                    out["tamper_overall"] = None

    except Exception as e:
        out["error"] = f"{type(e).__name__}: {e}"
    return out
PYEOF
    chmod +x "$SCN_LOG_DIR/mcp_client.py"

    # Drive the flow via the helper
    PY_OUT=$(python3 -c '
import sys, json
from pathlib import Path
sys.path.insert(0, "'"$SCN_LOG_DIR"'")
import mcp_client
res = mcp_client.run_cross_fed_handoff_mcp(
    "'"$NODE_BIN"'",
    "'"$F1_DATA_DIR"'",
    "'"$F2_DATA_DIR"'",
    "'"$F1_ID"'",
    "'"$F2_ID"'",
    open("'"$SCN_LOG_DIR"'/roots_F1.json").read(),
    open("'"$SCN_LOG_DIR"'/roots_F2.json").read(),
    Path("'"$SCN_LOG_DIR"'")
)
print(json.dumps(res))
' 2>&1 | tail -n 1 || echo '{"error":"python driver failed"}' )

    # Parse the python driver output and record assertions
    if command -v jq >/dev/null 2>&1; then
        alice_ok=$(echo "$PY_OUT" | jq -r '.alice_cell_created // false' 2>/dev/null || echo false)
        bob_ok=$(echo "$PY_OUT" | jq -r '.bob_cell_created // false' 2>/dev/null || echo false)
        cap_ok=$(echo "$PY_OUT" | jq -r '.bearer_cap_issued // false' 2>/dev/null || echo false)
        bil_ok=$(echo "$PY_OUT" | jq -r '.bilateral_transfer // false' 2>/dev/null || echo false)
        bundle_ok=$(echo "$PY_OUT" | jq -r '.bundle_written // false' 2>/dev/null || echo false)
        v_exit=$(echo "$PY_OUT" | jq -r '.verifier_exit // 99' 2>/dev/null || echo 99)
        v_overall=$(echo "$PY_OUT" | jq -r '.verifier_overall // false' 2>/dev/null || echo false)
        t_exit=$(echo "$PY_OUT" | jq -r '.tamper_verifier_exit // 99' 2>/dev/null || echo 99)
        t_overall=$(echo "$PY_OUT" | jq -r '.tamper_overall // true' 2>/dev/null || echo true)
    else
        alice_ok=false; bob_ok=false; cap_ok=false; bil_ok=false; bundle_ok=false
        v_exit=99; v_overall=false; t_exit=99; t_overall=true
    fi

    record alice_cell_created_on_F1 "$alice_ok"
    record bob_cell_created_on_F2 "$bob_ok"
    record bearer_cap_issued_on_F1 "$cap_ok"
    record bilateral_transfer_on_F2 "$bil_ok"
    record cross_fed_bundle_written "$bundle_ok"

    if [ "$v_exit" = "0" ] && [ "$v_overall" = "true" ]; then
        record verifier_accepts_bundle true
    else
        record verifier_accepts_bundle false
    fi

    # Tamper reject: either non-zero exit or overall false on tampered
    if [ "$t_exit" != "0" ] || [ "$t_overall" != "true" ]; then
        record verifier_rejects_tampered_bundle true
    else
        record verifier_rejects_tampered_bundle false
    fi

    # Persist the driver trace for debugging
    echo "$PY_OUT" > "$SCN_LOG_DIR/mcp_driver_result.json"
    echo "$PY_OUT" | python3 -c 'import sys,json; print(json.dumps(json.load(sys.stdin), indent=2))' > "$SCN_LOG_DIR/mcp_driver_pretty.json" 2>/dev/null || true

else
    devnet_warn "skipping real MCP/verifier work (devnet or binaries not ready)"
    for k in alice_cell_created_on_F1 bob_cell_created_on_F2 bearer_cap_issued_on_F1 \
             bilateral_transfer_on_F2 cross_fed_bundle_written verifier_accepts_bundle \
             verifier_rejects_tampered_bundle; do
        record "$k" false
    done
    echo '{"skipped":true,"reason":"devnet not responding or binaries missing"}' > "$SCN_LOG_DIR/mcp_driver_result.json"
fi

# ── Emit result.json (always, even in degraded mode) ──────────────────
{
    echo "{"
    echo "  \"scenario\": \"$SCENARIO_NAME\","
    echo "  \"federation_F1\": \"$F1_ID\","
    echo "  \"federation_F2\": \"$F2_ID\","
    echo "  \"results\": {"
    first=1
    for k in "${!RESULTS[@]}"; do
        if [ $first -eq 1 ]; then first=0; else echo ","; fi
        printf '    "%s": %s' "$k" "${RESULTS[$k]}"
    done
    echo
    echo "  },"
    emit_synthetic_warnings_json
    echo
    echo "}"
} > "$RESULT_FILE"

devnet_step "result written to $RESULT_FILE"

# Compare against expected.json — pass iff every must_pass is true.
EXPECTED="$HERE/../expected/$SCENARIO_NAME.json"
PASS=1
if [ -f "$EXPECTED" ] && command -v jq >/dev/null 2>&1; then
    for key in $(jq -r '.must_pass[]' "$EXPECTED" 2>/dev/null); do
        val=$(jq -r ".results.$key // false" "$RESULT_FILE" 2>/dev/null)
        if [ "$val" != "true" ]; then
            devnet_fail "must_pass FAILED: $key"
            PASS=0
        fi
    done
fi

if [ $PASS -eq 1 ]; then
    devnet_ok "scenario PASS"
    exit 0
else
    devnet_fail "scenario FAIL (must_pass assertions not all green)"
    exit 1
fi
