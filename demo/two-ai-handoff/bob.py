#!/usr/bin/env python3
"""Bob — the recipient.

Two modes:
  --mode=identity  → create Bob's identity, print {bob_pk, bob_cell}, exit.
                     run.sh invokes this BEFORE alice so Alice knows the
                     recipient pk to bake into her grant + bearer cap.

  --mode=exercise  → read the handoff URI Alice wrote to disk, enliven,
                     exercise the cap to do a Transfer. Drives steps 6+7.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from mcp_stdio import McpClient


def run_identity(args) -> int:
    state_dir = Path(args.state_dir)
    log_dir = state_dir / "logs"

    with McpClient(args.node_bin, args.data_dir, "bob.id", log_dir) as cli:
        agent = cli.tool("pyana_create_agent", {"name": "bob", "initial_balance": 1_000_000})
        bob_pk = agent["public_key"]
        bob_cell = agent["cell_id"]
        result = {"bob_pk": bob_pk, "bob_cell": bob_cell}
        (state_dir / "bob.identity.json").write_text(json.dumps(result, indent=2))
        print(json.dumps(result))
    return 0


def run_exercise(args) -> int:
    state_dir = Path(args.state_dir)
    log_dir = state_dir / "logs"
    uri_path = state_dir / "handoff.uri"
    if not uri_path.exists():
        print(f"[bob] no handoff URI at {uri_path}", file=sys.stderr)
        return 6

    handoff_uri = uri_path.read_text().strip()
    print(f"[bob] received handoff URI ({len(handoff_uri)} bytes)", file=sys.stderr)

    # Parse the URI. Today this is the `pyana+bearer:<json>` shim from
    # alice.py (see blocker-2). When the real `pyana-handoff:` compact
    # string lands, replace this with `HandoffCertificate::from_compact_string`-
    # equivalent parsing (likely a new MCP tool `pyana_decode_handoff_uri`).
    if handoff_uri.startswith("pyana+bearer:"):
        payload = json.loads(handoff_uri[len("pyana+bearer:") :])
    elif handoff_uri.startswith("pyana-handoff:"):
        print(
            "[bob] received a real pyana-handoff: URI but blocker-2 is unresolved; "
            "no decoder tool yet",
            file=sys.stderr,
        )
        return 6
    else:
        print(f"[bob] unknown URI scheme: {handoff_uri[:32]}", file=sys.stderr)
        return 6

    with McpClient(args.node_bin, args.data_dir, "bob.x", log_dir) as cli:
        # Reload Bob's identity (it was generated in --mode=identity).
        # The current MCP create_agent generates fresh keypairs every call,
        # so we re-create. Identity persistence across MCP sessions is a
        # separate gap (orthogonal to this demo).
        agent = cli.tool("pyana_create_agent", {"name": "bob", "initial_balance": 1_000_000})
        bob_cell = agent["cell_id"]
        alice_cell = payload["target_cell"]

        # Snapshot pre-exercise balances. The exercise tool will auto-insert
        # a remote stub for alice_cell (pre-funded), so the stub's balance
        # only becomes readable after `pyana_exercise_bearer_cap` runs.
        bob_pre = cli.tool("pyana_read_cell", {"cell_id": bob_cell})

        # ── Step 6: enliven + Step 7: exercise (one tool today) ───────────
        # Bob exercises the bearer cap to perform a Transfer from alice_cell
        # to bob_cell. The exercise tool now accepts an `effects` parameter
        # (Task C of the proof-gen wiring) — without it, the turn would be
        # a no-op and Bob wouldn't actually move any value.
        transfer_effect = {
            "type":   "transfer",
            "from":   payload["target_cell"],   # alice_cell
            # `bearer_pk` is bob's PUBLIC KEY (32-byte Ed25519 pk), not bob's
            # cell id. The cell id is derived as BLAKE3(pk || token_id) and
            # is what the ledger keys by; passing the pk here would credit a
            # different (auto-stubbed) cell, leaving bob_cell unchanged.
            "to":     bob_cell,
            "amount": args.amount,
        }
        exercise = cli.tool(
            "pyana_exercise_bearer_cap",
            {
                "target_cell":      payload["target_cell"],
                "method":           "transfer",
                "delegation_chain": payload["delegation_chain"],
                "bearer_pk":        payload["bearer_pk"],
                "expires_at":       payload["expires_at"],
                "permissions":      payload["permissions"],
                "effects":          [transfer_effect],
                # The delegator is Alice (the cell owner who signed the
                # bearer cap on her node). Without this, the exercise tool
                # would default to Bob's pk and signature verification
                # would fail against the wrong key.
                "delegator_pk":     payload["introducer_pk"],
            },
        )

        if not exercise.get("exercised"):
            print(f"[bob] step 7 FAILED: {exercise}", file=sys.stderr)
            (state_dir / "bob.exercise.json").write_text(json.dumps(exercise, indent=2))
            return 7

        # Capture the Effect VM proof from the exercise response and write
        # the standalone artifact for charlie.py / pyana-verifier.
        exercise_proof_hex = exercise.get("effect_vm_proof_hex")
        exercise_proof_pi = exercise.get("effect_vm_public_inputs") or []
        exercise_trace_rows = exercise.get("effect_vm_trace_rows") or []
        exercise_witness_hash = exercise.get("effect_vm_witness_hash_hex") or ""
        if exercise_proof_hex:
            (state_dir / "exercise.proof.json").write_text(json.dumps({
                "proof_hex":     exercise_proof_hex,
                "public_inputs": exercise_proof_pi,
                "trace_rows":    exercise_trace_rows,
                "witness_hash_hex": exercise_witness_hash,
                "vk_hash":       "auto",
                "source":        "pyana_exercise_bearer_cap",
            }, indent=2))
            print(f"[bob] wrote exercise proof artifact "
                  f"({len(exercise_proof_hex) // 2} proof bytes, "
                  f"{len(exercise_proof_pi)} public inputs, "
                  f"{len(exercise_trace_rows)} trace rows)", file=sys.stderr)
        else:
            print("[bob] WARNING: exercise turn returned no effect_vm_proof_hex",
                  file=sys.stderr)

        # Snapshot post-exercise balances. alice_cell is a remote-stub on
        # bob's ledger that the exercise tool pre-funded to ~1_000_000 (the
        # canonical balance lives on alice's node); after the Transfer that
        # stub balance should drop by `args.amount`, and bob_cell should
        # gain the same amount.
        bob_post = cli.tool("pyana_read_cell", {"cell_id": bob_cell})
        alice_stub_post = cli.tool("pyana_read_cell", {"cell_id": alice_cell})

        bob_pre_bal = bob_pre.get("balance") or 0
        bob_post_bal = bob_post.get("balance") or 0
        bob_delta = bob_post_bal - bob_pre_bal
        alice_stub_bal = alice_stub_post.get("balance")

        # Snapshot Bob's receipt chain so charlie/run.sh can inspect.
        chain = cli.tool("pyana_get_receipt_chain", {"limit": 50})

        result = {
            "exercise_turn_hash": exercise["turn_hash"],
            "exercised":          True,
            "receipt_chain":      chain,
            "transfer_amount":    args.amount,
            # Observable post-conditions on Bob's ledger. The
            # cross-process Transfer is local to Bob's view: alice_cell is
            # a remote-stub here, and the canonical alice balance change
            # lives on alice's node (not visible to this process).
            "bob_pre_balance":     bob_pre_bal,
            "bob_post_balance":    bob_post_bal,
            "bob_balance_delta":   bob_delta,
            "alice_stub_balance":  alice_stub_bal,
        }
        (state_dir / "bob.exercise.json").write_text(json.dumps(result, indent=2))
        print(json.dumps(result))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--node-bin", required=True)
    parser.add_argument("--data-dir", required=True)
    parser.add_argument("--state-dir", required=True)
    parser.add_argument("--mode", choices=["identity", "exercise"], required=True)
    parser.add_argument("--amount", type=int, default=100)
    args = parser.parse_args()
    if args.mode == "identity":
        return run_identity(args)
    return run_exercise(args)


if __name__ == "__main__":
    sys.exit(main())
