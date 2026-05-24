#!/usr/bin/env python3
"""Charlie — the structurally independent verifier.

Per `dev-philosophy/06-the-real-demo.md`, Charlie is *structurally untrusted*
and *structurally independent* of the prover. He runs as a different OS
process and — critically — a different *binary*: `pyana-verifier`, which
links only against `pyana-circuit` + `pyana-types` and carries no prover
state, no ledger, no executor, no program registry.

Charlie reads the proof artifacts written by alice.py / bob.py into
`state/{grant,exercise}.proof.json`, pipes them to `pyana-verifier` over
stdin (JSON mode), and reports the verifier's verdict. He does NOT speak
MCP. He does NOT touch a `pyana-node` process.

Output (stdout, single JSON object):

  {
    "grant_verified":     bool,
    "exercise_verified":  bool,
    "pid":                int,
    "independent_node":   true,    # no node process at all
    "independent_binary": true,    # pyana-verifier binary, different deps
    "verifier_binary":    "<path>",
    "verifier_pid":       int,     # last invocation's pid
    "blocker_notes":      [...]
  }
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path


def _zeros32() -> list[int]:
    return [0] * 32


def build_witnessed_chain(state_dir: Path) -> list[dict]:
    """Assemble a v1 WitnessedReceipt chain JSON from the per-turn proof
    artifacts emitted by alice.py / bob.py.

    v1 ships scope-(1) entries (proof + public_inputs, no inline witness
    bundle) because the MCP tool layer does not yet expose the raw trace.
    The replay-chain verifier treats this as a "verified" verdict — proof
    is sound, scope-(2) replay is deferred to the lane that plumbs the
    trace through generate_effect_vm_proof.

    The on-disk shape mirrors `pyana_turn::WitnessedReceipt` exactly so
    the verifier-side `ReplayEntry` deserialises it byte-for-byte.
    """
    chain: list[dict] = []
    for name, fname in [("grant", "grant.proof.json"), ("exercise", "exercise.proof.json")]:
        path = state_dir / fname
        if not path.exists():
            continue
        artifact = json.loads(path.read_text())
        proof_hex = artifact.get("proof_hex", "")
        pi = artifact.get("public_inputs", []) or []
        if not proof_hex:
            continue
        proof_bytes = list(bytes.fromhex(proof_hex))
        chain.append({
            # Minimal `receipt` placeholder — preserved as opaque JSON by
            # the verifier (it's `serde_json::Value` on the Rust side).
            "receipt": {"source": artifact.get("source", name)},
            "proof_bytes": proof_bytes,
            "public_inputs": [int(v) for v in pi],
            "witness_hash": _zeros32(),
        })
    return chain


def verify_chain_with_binary(verifier_bin: str, chain_path: Path) -> tuple[bool, str, int]:
    """Run `pyana-verifier replay-chain <chain.json>` and parse the verdict."""
    try:
        proc = subprocess.Popen(
            [verifier_bin, "replay-chain", str(chain_path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        stdout, stderr = proc.communicate(timeout=120)
    except FileNotFoundError:
        return False, f"verifier binary not found at {verifier_bin}", 0
    except subprocess.TimeoutExpired:
        proc.kill()
        return False, "replay-chain timed out", proc.pid

    rc = proc.returncode
    parsed: dict[str, object] = {}
    try:
        parsed = json.loads(stdout)
    except json.JSONDecodeError:
        parsed = {"summary": f"unparseable verifier output: stdout={stdout!r} stderr={stderr!r}"}
    overall = bool(parsed.get("overall_verified", False))
    summary = str(parsed.get("summary", ""))
    return overall and rc == 0, summary, proc.pid


def verify_proof_with_binary(
    verifier_bin: str, proof_hex: str, public_inputs: list[int]
) -> tuple[bool, str, int]:
    """Pipe a JSON request into the standalone pyana-verifier binary.

    Returns (verified, reason, pid). The pid is the child process's pid,
    captured for the structural-independence assertion in run.sh.
    """
    if not proof_hex:
        return False, "no proof_hex provided", 0

    request = json.dumps({
        "proof_hex":     proof_hex,
        "public_inputs": public_inputs,
        "vk_hash":       "auto",
    })

    try:
        proc = subprocess.Popen(
            [verifier_bin],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        stdout, stderr = proc.communicate(input=request, timeout=120)
    except FileNotFoundError:
        return False, f"verifier binary not found at {verifier_bin}", 0
    except subprocess.TimeoutExpired:
        proc.kill()
        return False, "verifier process timed out", proc.pid

    verifier_pid = proc.pid
    rc = proc.returncode

    # Exit-code contract: 0 = verified, 1 = rejected, 2 = error.
    # Verifier also prints a JSON {"verified": bool, "reason": "..."} on stdout.
    parsed: dict[str, object] = {}
    try:
        parsed = json.loads(stdout.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        parsed = {"verified": False, "reason": f"unparseable verifier output: {stdout!r}"}

    verified = bool(parsed.get("verified", False)) and rc == 0
    reason_raw = parsed.get("reason")
    reason = str(reason_raw) if reason_raw is not None else f"exit={rc} stderr={stderr.strip()[:200]}"
    return verified, reason, verifier_pid


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-dir", required=True)
    parser.add_argument(
        "--verifier-bin",
        required=True,
        help="Path to the standalone pyana-verifier binary "
             "(target/debug/pyana-verifier or target/release/pyana-verifier).",
    )
    # The node-bin / data-dir args are accepted for run.sh compatibility but
    # unused — charlie no longer speaks MCP.
    parser.add_argument("--node-bin", required=False, default=None)
    parser.add_argument("--data-dir", required=False, default=None)
    args = parser.parse_args()

    state_dir = Path(args.state_dir)
    alice_out = json.loads((state_dir / "alice.out.json").read_text())
    bob_out_path = state_dir / "bob.exercise.json"
    bob_out = json.loads(bob_out_path.read_text()) if bob_out_path.exists() else None

    blocker_notes: list[str] = []
    verifier_pid_last = 0

    # ── Step 4: verify the grant turn's proof ──────────────────────────────
    grant_proof_path = state_dir / "grant.proof.json"
    if grant_proof_path.exists():
        gp = json.loads(grant_proof_path.read_text())
        grant_verified, grant_reason, pid = verify_proof_with_binary(
            args.verifier_bin, gp["proof_hex"], gp["public_inputs"]
        )
        verifier_pid_last = pid or verifier_pid_last
        if not grant_verified:
            blocker_notes.append(f"grant proof rejected: {grant_reason}")
    else:
        blocker_notes.append("BLOCKER: no state/grant.proof.json artifact (was the grant tool's "
                             "effect_vm_proof_hex empty?)")
        grant_verified = False
        grant_reason = "no artifact"

    # ── Step 8: verify the exercise turn's proof ──────────────────────────
    exercise_proof_path = state_dir / "exercise.proof.json"
    if exercise_proof_path.exists():
        ep = json.loads(exercise_proof_path.read_text())
        exercise_verified, exercise_reason, pid = verify_proof_with_binary(
            args.verifier_bin, ep["proof_hex"], ep["public_inputs"]
        )
        verifier_pid_last = pid or verifier_pid_last
        if not exercise_verified:
            blocker_notes.append(f"exercise proof rejected: {exercise_reason}")
    else:
        blocker_notes.append("BLOCKER: no state/exercise.proof.json artifact")
        exercise_verified = False
        exercise_reason = "no artifact"

    # ── v1 replay-chain: WitnessedReceipt end-to-end ─────────────────────
    # Build a WR-chain JSON from the same proof artifacts and run the new
    # `pyana-verifier replay-chain` subcommand. This is the v1.D demo path
    # per WITNESSED-RECEIPT-CHAIN-DESIGN.md §8 step 4: "export a chain of
    # WitnessedReceipt to disk, and a tiny replayer invocation shows
    # scope-(2) replay end-to-end."
    chain = build_witnessed_chain(state_dir)
    chain_path = state_dir / "witnessed-chain.json"
    chain_path.write_text(json.dumps(chain, indent=2))
    if chain:
        replay_verified, replay_summary, replay_pid = verify_chain_with_binary(
            args.verifier_bin, chain_path
        )
        if not replay_verified:
            blocker_notes.append(f"replay-chain rejected: {replay_summary}")
    else:
        replay_verified = False
        replay_summary = "no WR-chain entries (no proof artifacts on disk)"
        replay_pid = 0
        blocker_notes.append("BLOCKER: cannot run replay-chain (no proof artifacts)")

    result = {
        "grant_verified":     grant_verified,
        "grant_reason":       grant_reason,
        "exercise_verified":  exercise_verified,
        "exercise_reason":    exercise_reason,
        "replay_chain_verified": replay_verified,
        "replay_chain_summary":  replay_summary,
        "replay_chain_entries":  len(chain),
        "replay_chain_pid":      replay_pid,
        "pid":                os.getpid(),
        "independent_node":   True,
        "independent_binary": True,
        "verifier_binary":    args.verifier_bin,
        "verifier_pid":       verifier_pid_last,
        "blocker_notes":      blocker_notes,
        "alice_grant_turn":   alice_out.get("grant_turn_hash"),
        "bob_exercise_turn":  (bob_out or {}).get("exercise_turn_hash"),
    }
    (state_dir / "charlie.verdict.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
