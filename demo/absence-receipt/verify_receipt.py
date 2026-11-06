#!/usr/bin/env python3
"""Authenticate the original receipt and compare every field with computed artifacts.

The caller must rerun the corpus to establish the computation. Comparing stored runner output
only authenticates metadata and its consistency, never a fresh execution.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PIN = "681f94fc638e5a7639aa410c34b984a12bcd8dfe"
FIELDS = {"v", "policy_blake3", "table_blake3", "corpus_mmr_root", "corpus_pin", "n", "count"}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def load(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_object)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("artifacts", type=Path, help="directory with documents.tsv and dfa-run.json")
    p.add_argument("--policy", type=Path, default=HERE / "policy.policy")
    p.add_argument("--table", type=Path, default=HERE / "absence-table.json")
    p.add_argument("--receipt", type=Path, default=HERE / "receipt.json")
    p.add_argument("--signature", type=Path)
    p.add_argument("--signers", type=Path, default=HERE / "allowed_signers")
    p.add_argument("--helper", type=Path, default=HERE / "../../target/release/absence-receipt")
    args = p.parse_args()
    body = args.receipt.read_bytes()
    signed = json.loads(body, object_pairs_hook=unique_object)
    if signed.keys() != FIELDS or signed["v"] != "absence-receipt-v1":
        raise ValueError("unknown or incomplete receipt format")
    subprocess.run(["ssh-keygen", "-Y", "verify", "-f", str(args.signers), "-I",
                    "absence-receipt@dregg", "-n", "absence-receipt", "-s",
                    str(args.signature or Path(str(args.receipt) + ".sig"))], input=body, check=True)
    helper = str(args.helper.resolve())
    mmr = json.loads(subprocess.check_output([helper, "mmr", str(args.artifacts / "documents.tsv")]))
    run = load(args.artifacts / "dfa-run.json")
    table = load(args.table)
    if run["table_well_formed"] is not True:
        raise ValueError("runner did not accept table well-formedness")
    for key in ("documents", "accepted", "count", "bytes", "num_states"):
        if type(run[key]) is not int or run[key] < 0:
            raise ValueError(f"invalid runner field: {key}")
    if (run["documents"] != mmr["documents"] or run["bytes"] != mmr["bytes"] or
            run["accepted"] + run["count"] != run["documents"] or
            run["num_states"] != table["num_states"]):
        raise ValueError("runner count, byte count, or table size is inconsistent")
    indices = run["rejected_indices"]
    if (not isinstance(indices, list) or len(indices) != run["count"] or
            any(type(i) is not int or i < 0 or i >= run["documents"] for i in indices) or
            indices != sorted(set(indices))):
        raise ValueError("invalid rejected document indices")
    expected = {
        "v": "absence-receipt-v1",
        "policy_blake3": subprocess.check_output([helper, "digest", str(args.policy)], text=True).strip(),
        "table_blake3": subprocess.check_output([helper, "digest", str(args.table)], text=True).strip(),
        "corpus_mmr_root": mmr["root"], "corpus_pin": PIN,
        "n": mmr["documents"], "count": run["count"],
    }
    changed = [k for k in sorted(FIELDS) if type(signed[k]) is not type(expected[k]) or signed[k] != expected[k]]
    if changed:
        raise ValueError("signed receipt differs from computed tuple: " + ", ".join(changed))
    print("VERIFIED signed tuple: " + json.dumps(expected, separators=(",", ":")))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as e:
        print(f"receipt verification FAILED: {e}", file=sys.stderr)
        sys.exit(1)
