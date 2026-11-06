#!/usr/bin/env python3
"""Verify a signed receipt AND re-execute its certificate, comparing the complete checked tuple.

This authenticates the demo key, not the checker binary or the transcript's provenance.
No key or checked-in artifact is created or changed.
"""
import argparse
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FIELDS = {"program_digest", "root", "pred", "count", "checker"}
CHECKER = "lake exe datalog-check (metatheory/DatalogCheck.lean)"


def receipt_fields(text):
    lines = text.splitlines()
    if not lines or lines[0] != "dregg datalog receipt v1":
        raise ValueError("unknown receipt format")
    result = {}
    for line in lines[1:]:
        key, sep, value = line.partition("=")
        if not sep or key not in FIELDS or key in result:
            raise ValueError(f"unknown, malformed or duplicate receipt field: {key!r}")
        result[key] = value
    if result.keys() != FIELDS or result["checker"] != CHECKER:
        raise ValueError("missing receipt field or unsupported checker")
    for key in ("program_digest", "root"):
        if not re.fullmatch(r"0x[0-9a-f]+", result[key]):
            raise ValueError(f"invalid {key}")
    for key in ("pred", "count"):
        if not re.fullmatch(r"0|[1-9][0-9]*", result[key]):
            raise ValueError(f"invalid {key}")
    return result


def checked_fields(output):
    patterns = {
        "program_digest": r"^program digest\s*: (0x[0-9a-f]+)$",
        "root": r"^  root\s*: (0x[0-9a-f]+)$",
        "pred": r"^  pred\s*: ([0-9]+)$",
        "count": r"^  claimed count\s*: ([0-9]+)$",
        "verdict": r"^verdict\s*: (.+)$",
    }
    result = {}
    for key, pattern in patterns.items():
        matches = re.findall(pattern, output, re.MULTILINE)
        if len(matches) != 1:
            raise ValueError(f"checker output must contain exactly one {key}")
        result[key] = matches[0]
    if result.pop("verdict") != "ACCEPT":
        raise ValueError("checker did not ACCEPT")
    result["checker"] = CHECKER
    return result


def compare(receipt, output):
    expected, actual = receipt_fields(receipt), checked_fields(output)
    changed = [key for key in sorted(FIELDS) if expected[key] != actual[key]]
    if changed:
        raise ValueError("signed receipt differs from checked certificate: " + ", ".join(changed))
    return actual


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("certificate", type=Path)
    p.add_argument("receipt", type=Path)
    p.add_argument("--signature", type=Path)
    p.add_argument("--signers", type=Path, default=HERE / "allowed_signers")
    p.add_argument("--checker", type=Path, default=HERE / "../../metatheory/.lake/build/bin/datalog-check")
    args = p.parse_args()
    body = args.receipt.read_bytes()
    receipt_fields(body.decode())
    subprocess.run(["ssh-keygen", "-Y", "verify", "-f", str(args.signers), "-I",
                    "datalog-governance@dregg", "-n", "dregg-datalog-receipt", "-s",
                    str(args.signature or Path(str(args.receipt) + ".sig"))], input=body, check=True)
    run = subprocess.run([str(args.checker.resolve()), str(args.certificate)],
                         text=True, capture_output=True, check=True)
    print(run.stdout, end="")
    result = compare(body.decode(), run.stdout)
    print(f"VERIFIED signed and checked tuple: count={result['count']} root={result['root']}")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, UnicodeError, subprocess.CalledProcessError) as e:
        print(f"receipt verification FAILED: {e}", file=sys.stderr)
        sys.exit(1)
