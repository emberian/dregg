# cross-app-e2e: Design for a Real Executor-Invoking Verifier

## What the current verify.py actually does

`verify.py` is a **structural coherence checker**, not a cryptographic
verifier. It:

1. Re-derives canonical commitments (schema, credential-set, bounty-state,
   resolve-target) using Python + BLAKE3 and checks they match stored artifacts.
2. Checks field equality between artifact files (e.g. `alice["bob_holder_id"]
   == bob_id["bob_cell"]`).
3. Checks structural shapes (kind strings, effect types, list lengths).
4. Runs negative tests by re-deriving commitments with forged inputs and
   asserting inequality.

It does **not**:
- Call `pyana-verifier` or any proof verifier.
- Inspect the `proof_hex` / `ProofBytes` blobs in `witness_blobs`.
- Verify that receipts are signed by a real cell key.
- Confirm any state transition was actually authorized by the executor.
- Detect hand-crafted `state/*.json` artifacts.

## What a real verifier would look like

### Prerequisite: production artifacts must carry verifiable proofs

Each agent script (alice.py, bob.py, carol.py, dan.py) must produce JSON
artifacts that include:
- `proof_hex`: hex-encoded STARK proof bytes.
- `public_inputs`: list of field elements that are the proof's PI.
- `vk_hash`: the verification key hash (or `"auto"` for the shared circuit VK).
- `receipt_sig_hex` + `signing_pk_hex`: Ed25519 signature over the canonical
  receipt hash and the cell's signing public key.

The `state/*.json` files already have a `witness_blobs[*].kind == "ProofBytes"`
field — the real version would require that field to contain a non-empty,
verifiable proof.

### Proposed `verify_real.py` structure

```python
#!/usr/bin/env python3
"""verify_real.py — executor-invoking cross-app-e2e verifier.

Augments verify.py's structural checks with:
  1. Per-turn STARK proof verification via `pyana-verifier`.
  2. Receipt signature verification via `pyana-verifier receipt-sig`.
  3. Replay-chain verification via `pyana-verifier replay-chain`.
  4. Negative tests: tampered proof must REJECT.
"""

import argparse, json, subprocess, sys, pathlib

def run(argv, stdin=None, timeout=120):
    p = subprocess.Popen(
        argv,
        stdin=subprocess.PIPE if stdin else None,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )
    out, err = p.communicate(input=stdin, timeout=timeout)
    return p.returncode, out, err

def verify_stark(verifier_bin, proof_hex, pi, vk_hash="auto"):
    """Call pyana-verifier with a STARK proof and PI; return (ok, reason)."""
    if not proof_hex:
        return False, "no proof_hex"
    req = json.dumps({"proof_hex": proof_hex, "public_inputs": pi, "vk_hash": vk_hash})
    rc, out, err = run([verifier_bin], stdin=req, timeout=120)
    try:
        parsed = json.loads(out.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        return False, f"unparseable: {out!r} {err!r}"
    return bool(parsed.get("verified")) and rc == 0, parsed.get("reason", "")

def verify_receipt_sig(verifier_bin, receipt_hash_hex, sig_hex, pk_hex):
    """Call pyana-verifier receipt-sig to check Ed25519 sig over receipt hash."""
    req = json.dumps({
        "receipt_hash_hex": receipt_hash_hex,
        "sig_hex": sig_hex,
        "signing_pk_hex": pk_hex,
    })
    rc, out, _ = run([verifier_bin, "receipt-sig"], stdin=req, timeout=30)
    try:
        parsed = json.loads(out.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        return False
    return bool(parsed.get("valid")) and rc == 0

def verify_replay_chain(verifier_bin, chain_path):
    """Call pyana-verifier replay-chain on a WitnessedReceipt chain."""
    rc, out, _ = run([verifier_bin, "replay-chain", str(chain_path)], timeout=120)
    try:
        parsed = json.loads(out)
    except json.JSONDecodeError:
        return False, out
    return bool(parsed.get("overall_verified")) and rc == 0, parsed.get("summary", "")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-dir", required=True)
    parser.add_argument("--expected", required=True)
    parser.add_argument("--verifier-bin", required=True,
                        help="Path to pyana-verifier binary")
    parser.add_argument("--out", required=True)
    args = parser.parse_args()

    state_dir = pathlib.Path(args.state_dir)
    results = {}

    # ── Re-run all structural checks from verify.py ──────────────────
    # (import verify.verify(...) directly)
    from verify import verify as structural_verify
    results.update(structural_verify(str(state_dir)))

    # ── Per-turn STARK proof verification ────────────────────────────
    # Turns that must carry a verifiable proof:
    #   bob.register.json   — attested nameservice registration proof
    #   dan.claim.json      — subscription claim proof
    #   dan.fulfill.json    — subscription fulfill proof
    #   carol.settle.json   — subscription settle proof

    for artifact_name, label in [
        ("bob.register.json", "bob_register_proof_verifies"),
        ("dan.claim.json",    "dan_claim_proof_verifies"),
        ("dan.fulfill.json",  "dan_fulfill_proof_verifies"),
        ("carol.settle.json", "carol_settle_proof_verifies"),
    ]:
        path = state_dir / artifact_name
        artifact = json.loads(path.read_text()) if path.exists() else {}
        # witness_blobs[0] must be kind=ProofBytes with non-empty proof_hex
        blobs = artifact.get("witness_blobs", [])
        proof_hex = ""
        pi = []
        for blob in blobs:
            if blob.get("kind") == "ProofBytes":
                proof_hex = blob.get("proof_hex", "")
                pi = blob.get("public_inputs", [])
                break
        ok, reason = verify_stark(args.verifier_bin, proof_hex, pi)
        results[label] = ok

    # ── Receipt signature verification ───────────────────────────────
    # Each receipt must carry receipt_hash_hex + sig_hex + signing_pk_hex.
    for artifact_name, label in [
        ("bob.register.json",    "bob_register_receipt_sig_valid"),
        ("carol.post.json",      "carol_post_receipt_sig_valid"),
        ("dan.claim.json",       "dan_claim_receipt_sig_valid"),
    ]:
        path = state_dir / artifact_name
        artifact = json.loads(path.read_text()) if path.exists() else {}
        ok = verify_receipt_sig(
            args.verifier_bin,
            artifact.get("receipt_hash_hex", ""),
            artifact.get("sig_hex", ""),
            artifact.get("signing_pk_hex", ""),
        )
        results[label] = ok

    # ── Replay-chain verification ─────────────────────────────────────
    # Build the chain from all per-turn proof artifacts and run replay-chain.
    chain_entries = []
    for name, fname in [
        ("bob_register", "bob.register.json"),
        ("carol_post",   "carol.post.json"),
        ("dan_claim",    "dan.claim.json"),
        ("dan_fulfill",  "dan.fulfill.json"),
        ("carol_settle", "carol.settle.json"),
    ]:
        p = state_dir / fname
        if not p.exists():
            continue
        artifact = json.loads(p.read_text())
        proof_hex = ""
        pi = []
        for blob in artifact.get("witness_blobs", []):
            if blob.get("kind") == "ProofBytes":
                proof_hex = blob.get("proof_hex", "")
                pi = blob.get("public_inputs", [])
                break
        if not proof_hex:
            continue
        chain_entries.append({
            "receipt": {"source": name},
            "proof_bytes": list(bytes.fromhex(proof_hex)),
            "public_inputs": [int(v) for v in pi],
            "witness_hash": [0] * 32,
        })

    chain_path = state_dir / "witnessed-chain.json"
    chain_path.write_text(json.dumps(chain_entries, indent=2))
    if chain_entries:
        ok, summary = verify_replay_chain(args.verifier_bin, chain_path)
        results["cross_app_replay_chain_verifies"] = ok
    else:
        results["cross_app_replay_chain_verifies"] = False

    # ── Negative test: tampered proof must REJECT ─────────────────────
    # Take dan.claim.json's proof_hex, flip one byte, confirm rejection.
    claim = json.loads((state_dir / "dan.claim.json").read_text()) \
        if (state_dir / "dan.claim.json").exists() else {}
    for blob in claim.get("witness_blobs", []):
        if blob.get("kind") == "ProofBytes" and blob.get("proof_hex"):
            raw = bytearray(bytes.fromhex(blob["proof_hex"]))
            if raw:
                raw[len(raw) // 2] ^= 0xFF   # flip middle byte
            tampered_hex = raw.hex()
            ok, _ = verify_stark(args.verifier_bin, tampered_hex, blob.get("public_inputs", []))
            results["rejects_tampered_dan_claim_proof"] = not ok
            break

    # ── Collate verdict ───────────────────────────────────────────────
    with open(args.expected) as f:
        expected = json.load(f)

    must_pass_failures = [c for c in expected["must_pass"] if not results.get(c, False)]
    must_not_pass_failures = [c for c in expected.get("must_not_pass", [])
                              if not results.get(c, False)]

    verdict = {
        "results": dict(sorted(results.items())),
        "must_pass_failures": must_pass_failures,
        "must_not_pass_failures": must_not_pass_failures,
        "passed": not must_pass_failures and not must_not_pass_failures,
    }
    with open(args.out, "w") as f:
        json.dump(verdict, f, indent=2, sort_keys=True)
    print(json.dumps(verdict, indent=2, sort_keys=True))
    return 0 if verdict["passed"] else 1

if __name__ == "__main__":
    sys.exit(main())
```

### New must_pass entries for `expected.json`

When the real verifier is wired, add these to `expected.json`:

```json
"must_pass": [
  "...(existing)...",
  "bob_register_proof_verifies",
  "dan_claim_proof_verifies",
  "dan_fulfill_proof_verifies",
  "carol_settle_proof_verifies",
  "bob_register_receipt_sig_valid",
  "carol_post_receipt_sig_valid",
  "dan_claim_receipt_sig_valid",
  "cross_app_replay_chain_verifies"
],
"must_not_pass": [
  "...(existing)...",
  "rejects_tampered_dan_claim_proof"
]
```

### What the agent scripts must change to support this

Each of `alice.py`, `bob.py`, `carol.py`, `dan.py` must invoke `pyana-node`
in a mode that returns:
- `witness_blobs[0].proof_hex` — actual STARK proof hex.
- `witness_blobs[0].public_inputs` — field elements.
- `receipt_hash_hex` — canonical receipt hash.
- `sig_hex` — Ed25519 signature over `receipt_hash_hex`.
- `signing_pk_hex` — the cell's current public key.

The `pyana-node` CLI (or MCP tool) must expose these fields in turn output.
This is the primary unblocking work.

### Sequencing

1. Confirm `pyana-verifier` accepts `{"proof_hex": "...", "public_inputs":
   [...], "vk_hash": "auto"}` from stdin — this is already the charlie.py
   protocol in `two-ai-handoff`.
2. Add `receipt-sig` subcommand to `pyana-verifier` (or use existing path).
3. Update agent scripts to emit `proof_hex` + `receipt_hash_hex` + `sig_hex`.
4. Replace `verify.py` invocation in `run.sh` with `verify_real.py`.
5. Expand `expected.json` must_pass list as above.
