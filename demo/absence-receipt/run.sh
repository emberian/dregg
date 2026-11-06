#!/usr/bin/env bash
# Default: reproduce the public corpus computation and compare the ORIGINAL signed receipt.
# verify: check signature and stored metadata only; no claim of fresh corpus computation.
# generate: reproduce into fresh outputs without requiring the current receipt (maintainers).
set -euo pipefail
PIN=681f94fc638e5a7639aa410c34b984a12bcd8dfe
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
MT="$REPO/metatheory"
AR="${AR:-$REPO/target/release/absence-receipt}"
DFARUN="${DFARUN:-$MT/.lake/build/bin/dfa-run}"
POLICY="$HERE/policy.policy"
MODE="${1:-replay}"
case "$MODE" in replay|verify|generate) ;; *) echo 'usage: run.sh [replay|verify|generate]' >&2; exit 2 ;; esac
WORK="${WORK:-$(mktemp -d "${TMPDIR:-/tmp}/absence-receipt.XXXXXX")}"
mkdir -p "$WORK"
[[ -z "$(ls -A "$WORK")" ]] || { echo "WORK must be empty: $WORK" >&2; exit 2; }
WORK="$(cd "$WORK" && pwd)"
echo "output: $WORK"
now() { perl -MTime::HiRes=time -e 'printf "%.3f\n", time'; }
leg() { local name="$1"; shift; local t0; t0=$(now); "$@"; echo "$name $(echo "$t0 $(now)" | awk '{printf "%.3f", $2-$1}')" >> "$WORK/timings.txt"; }
[[ -x "$AR" ]] || cargo build -q --release -p absence-receipt --manifest-path "$REPO/Cargo.toml"
verify() {
  python3 -I "$HERE/verify_receipt.py" "$WORK" --policy "$POLICY" --table "$1" --helper "$AR"
}
if [[ "$MODE" = verify ]]; then
  gunzip -c "$HERE/documents.tsv.gz" > "$WORK/documents.tsv"
  cp "$HERE/dfa-run.json" "$WORK/dfa-run.json"
  verify "$HERE/absence-table.json"
  echo 'Metadata authenticated and consistent. Corpus computation was NOT rerun; use run.sh replay.'
  exit 0
fi
if [[ "$MODE" = replay ]] && ! cargo nextest --version >/dev/null 2>&1; then
  echo 'Full replay requires cargo-nextest. Install it before running this command.' >&2
  exit 2
fi
# A native override is useful for an isolated builder; by default Lake refreshes all required
# Lean targets, including the descriptor emitter that a cold policyc-only build would omit.
if [[ -z "${POLICYC:-}" ]]; then
  (cd "$MT" && lake build policyc dfa-run Dregg2.Circuit.Emit.DfaRoutingTableRoute8)
  POLICYC="$MT/.lake/build/bin/policyc"
fi
if [[ -z "${INDEX:-}" ]]; then
  INDEX="$WORK/index"
  git init -q "$INDEX"
  git -C "$INDEX" remote add origin https://github.com/rust-lang/crates.io-index.git
  git -C "$INDEX" fetch --depth 1 origin "$PIN"
  git -C "$INDEX" -c advice.detachedHead=false checkout -q --detach "$PIN"
fi
INDEX="$(cd "$INDEX" && pwd)"
[[ "$(git -C "$INDEX" rev-parse HEAD)" = "$PIN" ]] || { echo "INDEX is not at $PIN" >&2; exit 1; }
[[ -x "$DFARUN" ]] || (cd "$MT" && lake build dfa-run)
leg select "$AR" select "$INDEX" 100000 "$WORK/manifest.txt"
leg hashes "$AR" hashes "$INDEX" "$WORK/manifest.txt" "$WORK/documents.tsv"
gunzip -c "$HERE/documents.tsv.gz" | cmp - "$WORK/documents.tsv"
leg mmr "$AR" mmr "$WORK/documents.tsv" > "$WORK/mmr.json"
leg compile "$POLICYC" compile "$POLICY" --pattern secrets --absence > "$WORK/absence-table.json"
if [[ "$MODE" != generate ]]; then cmp "$WORK/absence-table.json" "$HERE/absence-table.json"; fi
leg dfa-run "$DFARUN" "$WORK/absence-table.json" --corpus "$INDEX" "$WORK/manifest.txt" > "$WORK/dfa-run.json"
leg rust-count "$AR" count "$WORK/absence-table.json" "$INDEX" "$WORK/manifest.txt" > "$WORK/rust-count.json"
python3 -I - "$WORK" <<'PY'
import json, pathlib, sys
p = pathlib.Path(sys.argv[1])
a = json.loads((p/'dfa-run.json').read_text()); b = json.loads((p/'rust-count.json').read_text())
for k in ('documents', 'count', 'rejected_indices'):
    if a[k] != b[k]: raise SystemExit(f'Lean and Rust disagree on {k}')
print(f'Lean and Rust agree: {a["documents"]} documents, {a["count"]} rejected')
PY
printf -- '-----BEGIN OPENSSH %s-----\n' 'PRIVATE KEY' > "$WORK/pem-header.txt"
control() {
  local actual; actual=$("$DFARUN" "$WORK/absence-table.json" "$1")
  [[ "$actual" = "$2" ]] || { echo "control $(basename "$1"): expected $2, got $actual" >&2; exit 1; }
  echo "control $(basename "$1"): $actual"
}
control "$HERE/controls/aws-key.txt" REJECT
control "$HERE/controls/near-miss.txt" ACCEPT
control "$WORK/pem-header.txt" REJECT
cmp "$INDEX/3/c/cxr" "$HERE/record-1598.jsonl"
emit_record() { (cd "$MT" && lake env lean --run ../demo/absence-receipt/EmitRecord.lean "$WORK/absence-table.json" "$INDEX/3/c/cxr" "$WORK/record-1598.descriptor.json"); }
leg emit-record emit_record
if [[ "$MODE" != generate ]]; then cmp "$WORK/record-1598.descriptor.json" "$HERE/record-1598.descriptor.json"; fi
leg receipt "$AR" receipt "$POLICY" "$WORK/absence-table.json" "$WORK/documents.tsv" "$WORK/dfa-run.json" "$PIN" "$WORK/receipt.json"
if [[ "$MODE" != generate ]]; then
  leg verify verify "$WORK/absence-table.json"
  echo 'Full corpus computation agrees with the original signed receipt.'
  record_proof() { (cd "$REPO" && cargo nextest run -p dregg-circuit --release --test absence_receipt_record -E 'test(absence_record_proves_and_verifies)' --success-output immediate); }
  leg record-proof record_proof 2>&1 | tee "$WORK/record-proof.log"
else
  echo 'Generated unsigned artifacts only; original receipt and trust anchor are unchanged.'
fi
cat "$WORK/timings.txt"
