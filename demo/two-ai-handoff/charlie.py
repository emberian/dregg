#!/usr/bin/env python3
"""Charlie — the structurally independent verifier.

Charlie's job is to read the artifacts produced by alice + bob + silver-helper
and run every verification check by shelling to:

  * `pyana-verifier` — the standalone STARK verifier binary
  * `silver-helper`  — the demo-side helper that mirrors the canonical
                       executor checks for `Authorization::CapTpDelivered`,
                       `SovereignCellWitness`, slot caveats, and γ.2
                       bilateral binding

Charlie does NOT speak MCP and does NOT touch a `pyana-node` process. He
runs strictly off-disk artifacts.

The verdict JSON shape:

  {
    "grant_verified":               bool,
    "exercise_verified":            bool,
    "replay_chain_verified":        bool,
    "captp_delivered_verified":     bool,
    "captp_delivered_tampered_rejected": bool,
    "sovereign_witness_self_verifies":   bool,
    "sovereign_witness_tampered_rejected": bool,
    "slot_caveat_first_write_ok":   bool,
    "slot_caveat_rewrite_rejected": bool,
    "slot_caveat_renewal_ok":       bool,
    "bilateral_verified":           bool,
    "bilateral_tampered_rejected":  bool,
    "verifier_binary":              "<path>",
    "silver_helper_binary":         "<path>",
    "pid":                          int,
    "independent_node":             true,
    "independent_binary":           true,
    "blocker_notes":                [...]
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


def run_proc(argv: list[str], stdin: str | None = None, timeout: int = 120) -> tuple[int, str, str]:
    """Run a subprocess; return (rc, stdout, stderr)."""
    try:
        proc = subprocess.Popen(
            argv,
            stdin=subprocess.PIPE if stdin is not None else None,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        stdout, stderr = proc.communicate(input=stdin, timeout=timeout)
    except FileNotFoundError as e:
        return 127, "", f"binary not found: {e}"
    except subprocess.TimeoutExpired:
        proc.kill()
        return 124, "", "timeout"
    return proc.returncode, stdout, stderr


def build_witnessed_chain(state_dir: Path) -> list[dict]:
    """Build a v1 WitnessedReceipt chain from the per-turn proof artifacts."""
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
        trace_rows = artifact.get("trace_rows") or []
        witness_hash_hex = artifact.get("witness_hash_hex") or ""

        if trace_rows and witness_hash_hex:
            witness_bundle = {
                "trace_rows": [[int(c) for c in row] for row in trace_rows],
                "availability": "Inline",
            }
            witness_hash = list(bytes.fromhex(witness_hash_hex))
            chain.append({
                "receipt": {"source": artifact.get("source", name)},
                "proof_bytes": proof_bytes,
                "public_inputs": [int(v) for v in pi],
                "witness_bundle": witness_bundle,
                "witness_hash": witness_hash,
            })
        else:
            chain.append({
                "receipt": {"source": artifact.get("source", name)},
                "proof_bytes": proof_bytes,
                "public_inputs": [int(v) for v in pi],
                "witness_hash": _zeros32(),
            })
    return chain


def verify_proof(verifier_bin: str, proof_hex: str, pi: list[int]) -> tuple[bool, str]:
    if not proof_hex:
        return False, "no proof_hex"
    req = json.dumps({"proof_hex": proof_hex, "public_inputs": pi, "vk_hash": "auto"})
    rc, stdout, stderr = run_proc([verifier_bin], stdin=req, timeout=120)
    try:
        parsed = json.loads(stdout.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        parsed = {"verified": False, "reason": f"unparseable: stdout={stdout!r} stderr={stderr!r}"}
    return bool(parsed.get("verified", False)) and rc == 0, str(parsed.get("reason", ""))


def verify_replay_chain(verifier_bin: str, chain_path: Path) -> tuple[bool, str]:
    rc, stdout, stderr = run_proc([verifier_bin, "replay-chain", str(chain_path)], timeout=120)
    try:
        parsed = json.loads(stdout)
    except json.JSONDecodeError:
        parsed = {"summary": f"unparseable: {stdout!r} {stderr!r}"}
    return bool(parsed.get("overall_verified", False)) and rc == 0, str(parsed.get("summary", ""))


def verify_bilateral(verifier_bin: str, bundle_path: Path) -> tuple[bool, str]:
    """Run `pyana-verifier bilateral-pair <bundle>` and parse verdict."""
    rc, stdout, stderr = run_proc([verifier_bin, "bilateral-pair", str(bundle_path)], timeout=120)
    try:
        parsed = json.loads(stdout)
    except json.JSONDecodeError:
        parsed = {"reason": f"unparseable: {stdout!r} {stderr!r}", "verified": False}
    return bool(parsed.get("verified", False)) and rc == 0, str(parsed.get("reason", ""))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-dir", required=True)
    parser.add_argument("--verifier-bin", required=True)
    parser.add_argument("--silver-helper-bin", required=True,
                        help="Path to the demo's silver-helper binary")
    # Compatibility-only:
    parser.add_argument("--node-bin", required=False, default=None)
    parser.add_argument("--data-dir", required=False, default=None)
    args = parser.parse_args()

    state_dir = Path(args.state_dir)
    blocker_notes: list[str] = []

    # ─── grant + exercise STARK proofs ────────────────────────────────────
    grant_proof_path = state_dir / "grant.proof.json"
    exercise_proof_path = state_dir / "exercise.proof.json"

    if grant_proof_path.exists():
        gp = json.loads(grant_proof_path.read_text())
        grant_verified, grant_reason = verify_proof(args.verifier_bin, gp["proof_hex"], gp["public_inputs"])
        if not grant_verified:
            blocker_notes.append(f"grant proof rejected: {grant_reason}")
    else:
        grant_verified, grant_reason = False, "no grant.proof.json"
        blocker_notes.append(grant_reason)

    if exercise_proof_path.exists():
        ep = json.loads(exercise_proof_path.read_text())
        exercise_verified, exercise_reason = verify_proof(args.verifier_bin, ep["proof_hex"], ep["public_inputs"])
        if not exercise_verified:
            blocker_notes.append(f"exercise proof rejected: {exercise_reason}")
    else:
        exercise_verified, exercise_reason = False, "no exercise.proof.json"
        blocker_notes.append(exercise_reason)

    # ─── replay-chain ──────────────────────────────────────────────────────
    chain = build_witnessed_chain(state_dir)
    chain_path = state_dir / "witnessed-chain.json"
    chain_path.write_text(json.dumps(chain, indent=2))
    scope_per_entry = [
        "scope-2" if entry.get("witness_bundle") is not None else "scope-1"
        for entry in chain
    ]
    if chain:
        replay_verified, replay_summary = verify_replay_chain(args.verifier_bin, chain_path)
        if not replay_verified:
            blocker_notes.append(f"replay-chain rejected: {replay_summary}")
    else:
        replay_verified, replay_summary = False, "no chain entries"
        blocker_notes.append(replay_summary)

    # ─── CapTpDelivered (silver-helper verify) ────────────────────────────
    rc_ok, stdout, _ = run_proc([args.silver_helper_bin, "verify-captp-delivered",
                                 "--state-dir", str(state_dir)])
    try:
        captp_verdict = json.loads(stdout)
    except json.JSONDecodeError:
        captp_verdict = {"verified": False}
        blocker_notes.append(f"captp-delivered verify unparseable: {stdout!r}")
    captp_delivered_verified = bool(captp_verdict.get("verified", False)) and rc_ok == 0

    # The must_not_pass: tampered signature must REJECT.
    rc_tamper, stdout_t, _ = run_proc([args.silver_helper_bin, "verify-captp-delivered-tampered",
                                       "--state-dir", str(state_dir)])
    try:
        tamper_verdict = json.loads(stdout_t)
    except json.JSONDecodeError:
        tamper_verdict = {"tampered_signature_accepted": True}
        blocker_notes.append("tampered captp-delivered verdict unparseable")
    # `expected_rejected` should be true; the binary exits 0 only when correctly rejected.
    captp_tampered_rejected = (not bool(tamper_verdict.get("tampered_signature_accepted", True))
                               and rc_tamper == 0)

    # ─── Sovereign witness (from silver.sovereign-witness.json) ───────────
    sov_path = state_dir / "silver.sovereign-witness.json"
    if sov_path.exists():
        sov = json.loads(sov_path.read_text())
        sovereign_witness_self_verifies = bool(sov.get("self_verifies", False))
        sovereign_witness_tampered_rejected = not bool(sov.get("tampered_self_verifies", True))
    else:
        sovereign_witness_self_verifies = False
        sovereign_witness_tampered_rejected = False
        blocker_notes.append("no silver.sovereign-witness.json")

    # ─── Slot caveat (from silver.slot-caveat.json) ───────────────────────
    cav_path = state_dir / "silver.slot-caveat.json"
    if cav_path.exists():
        cav = json.loads(cav_path.read_text())
        slot_caveat_first_write_ok = bool(cav.get("first_write_ok", False))
        slot_caveat_rewrite_rejected = bool(cav.get("rewrite_rejected", False))
        slot_caveat_renewal_ok = bool(cav.get("renewal_ok", False))
    else:
        slot_caveat_first_write_ok = False
        slot_caveat_rewrite_rejected = False
        slot_caveat_renewal_ok = False
        blocker_notes.append("no silver.slot-caveat.json")

    # ─── γ.2 bilateral binding ────────────────────────────────────────────
    bilat_meta_path = state_dir / "silver.bilateral.json"
    if bilat_meta_path.exists():
        bilat = json.loads(bilat_meta_path.read_text())
        bundle = Path(bilat["bundle_path"])
        bundle_t = Path(bilat["bundle_path_tampered"])
        bilateral_verified, bilateral_reason = verify_bilateral(args.verifier_bin, bundle)
        bilateral_tamper_accepted, bilateral_tamper_reason = verify_bilateral(args.verifier_bin, bundle_t)
        bilateral_tampered_rejected = not bilateral_tamper_accepted
        if not bilateral_verified:
            blocker_notes.append(f"bilateral bundle rejected: {bilateral_reason}")
        if bilateral_tamper_accepted:
            blocker_notes.append(f"bilateral tampered bundle WRONGLY accepted: {bilateral_tamper_reason}")
    else:
        bilateral_verified = False
        bilateral_tampered_rejected = False
        blocker_notes.append("no silver.bilateral.json")

    # ─── interaction-matrix lane: slot-caveat-suite ──────────────────────
    suite_path = state_dir / "silver.slot-caveat-suite.json"
    slot_caveat_suite: dict = {}
    if suite_path.exists():
        suite = json.loads(suite_path.read_text())
        for case in suite.get("cases", []):
            cname = case.get("constraint", "?")
            slot_caveat_suite[cname] = {
                "positive_ok": bool(case.get("positive_ok", False)),
                "negative_rejected": bool(case.get("negative_rejected", False)),
                "positive_reason": case.get("positive_reason", ""),
                "negative_reason": case.get("negative_reason", ""),
            }
            if not case.get("positive_ok", False):
                blocker_notes.append(f"slot-caveat-suite[{cname}] positive failed: {case.get('positive_reason', '')}")
            if not case.get("negative_rejected", False):
                blocker_notes.append(f"slot-caveat-suite[{cname}] negative WRONGLY accepted: {case.get('negative_reason', '')}")
    else:
        blocker_notes.append("no silver.slot-caveat-suite.json (imatrix lane gap)")

    # ─── interaction-matrix lane: credential-set auth ────────────────────
    cset_path = state_dir / "silver.credential-set-auth.json"
    if cset_path.exists():
        cset = json.loads(cset_path.read_text())
        credential_set_reproducible = bool(cset.get("commitment_reproducible", False))
        credential_set_distinct_schemas = bool(cset.get("distinct_schemas_distinct_commitments", False))
        credential_set_distinct_issuers = bool(cset.get("distinct_issuers_distinct_commitments", False))
        if not credential_set_reproducible:
            blocker_notes.append("credential-set commitment not reproducible")
        if not credential_set_distinct_schemas:
            blocker_notes.append("credential-set: distinct schemas collided in commitment")
        if not credential_set_distinct_issuers:
            blocker_notes.append("credential-set: distinct issuers collided in commitment")
    else:
        credential_set_reproducible = False
        credential_set_distinct_schemas = False
        credential_set_distinct_issuers = False
        blocker_notes.append("no silver.credential-set-auth.json (imatrix lane gap)")

    # ─── interaction-matrix lane: Effect::Introduce bilateral bundle ─────
    intro_path = state_dir / "silver.introduce.json"
    if intro_path.exists():
        intro = json.loads(intro_path.read_text())
        introduce_schedule_has_one = bool(intro.get("schedule_has_one_introduce", False))
        intro_bundle = Path(intro["bundle_path"])
        intro_bundle_t = Path(intro["bundle_path_tampered"])
        intro_verified, intro_reason = verify_bilateral(args.verifier_bin, intro_bundle)
        intro_tamper_accepted, intro_tamper_reason = verify_bilateral(args.verifier_bin, intro_bundle_t)
        introduce_bilateral_verified = intro_verified
        introduce_bilateral_tampered_rejected = not intro_tamper_accepted
        if not introduce_schedule_has_one:
            blocker_notes.append("introduce schedule does not have exactly one Introduce entry")
        if not introduce_bilateral_verified:
            blocker_notes.append(f"introduce bilateral bundle rejected: {intro_reason}")
        if intro_tamper_accepted:
            blocker_notes.append(f"introduce tampered bundle WRONGLY accepted: {intro_tamper_reason}")
    else:
        introduce_schedule_has_one = False
        introduce_bilateral_verified = False
        introduce_bilateral_tampered_rejected = False
        blocker_notes.append("no silver.introduce.json (imatrix lane gap)")

    # ─── Assemble verdict ─────────────────────────────────────────────────
    result = {
        "grant_verified": grant_verified,
        "grant_reason": grant_reason,
        "exercise_verified": exercise_verified,
        "exercise_reason": exercise_reason,
        "replay_chain_verified": replay_verified,
        "replay_chain_summary": replay_summary,
        "replay_chain_entries": len(chain),
        "replay_chain_scope": scope_per_entry,
        "captp_delivered_verified": captp_delivered_verified,
        "captp_delivered_details": captp_verdict,
        "captp_delivered_tampered_rejected": captp_tampered_rejected,
        "sovereign_witness_self_verifies": sovereign_witness_self_verifies,
        "sovereign_witness_tampered_rejected": sovereign_witness_tampered_rejected,
        "slot_caveat_first_write_ok": slot_caveat_first_write_ok,
        "slot_caveat_rewrite_rejected": slot_caveat_rewrite_rejected,
        "slot_caveat_renewal_ok": slot_caveat_renewal_ok,
        "bilateral_verified": bilateral_verified,
        "bilateral_tampered_rejected": bilateral_tampered_rejected,
        "slot_caveat_suite": slot_caveat_suite,
        "credential_set_reproducible": credential_set_reproducible,
        "credential_set_distinct_schemas": credential_set_distinct_schemas,
        "credential_set_distinct_issuers": credential_set_distinct_issuers,
        "introduce_schedule_has_one_introduce": introduce_schedule_has_one,
        "introduce_bilateral_verified": introduce_bilateral_verified,
        "introduce_bilateral_tampered_rejected": introduce_bilateral_tampered_rejected,
        "pid": os.getpid(),
        "independent_node": True,
        "independent_binary": True,
        "verifier_binary": args.verifier_bin,
        "silver_helper_binary": args.silver_helper_bin,
        "blocker_notes": blocker_notes,
    }
    (state_dir / "charlie.verdict.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
