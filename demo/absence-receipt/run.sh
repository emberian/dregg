#!/usr/bin/env bash
# Demo (a), the absence receipt: every leg, timed. See README.md.
#
#   INDEX=/path/to/crates.io-index ./run.sh          # full pipeline (needs the corpus clone)
#   ./run.sh verify                                  # stranger's check: no clone needed
#
# The corpus is crates.io-index at PIN; clone it into a fresh empty directory (it is untrusted
# data; nothing in it is executed):
#   git init idx && cd idx && git remote add origin https://github.com/rust-lang/crates.io-index.git
#   git fetch --depth 1 origin $PIN && git checkout FETCH_HEAD
set -euo pipefail
PIN=681f94fc638e5a7639aa410c34b984a12bcd8dfe
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
MT="$REPO/metatheory"
AR="$REPO/target/release/absence-receipt"
DFARUN="$MT/.lake/build/bin/dfa-run"
WORK="${WORK:-$(mktemp -d "${TMPDIR:-/tmp}/absence-receipt.XXXXXX")}"
now() { perl -MTime::HiRes=time -e 'printf "%.2f\n", time'; }
leg() { local name="$1"; shift; local t0; t0=$(now); "$@"; echo "$name $(echo "$t0 $(now)" | awk '{printf "%.1f", $2-$1}')" >> "$WORK/timings.txt"; }

verify() {
  # 1. the signature over the receipt body
  ssh-keygen -Y verify -f "$HERE/allowed_signers" -I absence-receipt@dregg -n absence-receipt \
    -s "$HERE/receipt.json.sig" < "$HERE/receipt.json"
  # 2. the corpus root from the checked-in document hashes (no clone needed)
  gunzip -c "$HERE/documents.tsv.gz" > "$WORK/documents.tsv"
  local root; root=$("$AR" mmr "$WORK/documents.tsv" | sed 's/.*"root":"\([0-9a-f]*\)".*/\1/')
  grep -q "\"corpus_mmr_root\":\"$root\"" "$HERE/receipt.json" && echo "corpus root $root matches the receipt"
  # 3. the digests of the policy and table the receipt names
  local pd td; pd=$(b3sum_of "$HERE/policy.txt"); td=$(b3sum_of "$HERE/absence-table.json")
  grep -q "\"policy_blake3\":\"$pd\"" "$HERE/receipt.json" && echo "policy digest matches"
  grep -q "\"table_blake3\":\"$td\"" "$HERE/receipt.json" && echo "table digest matches"
}
b3sum_of() { "$AR" digest "$1"; }

cargo build -q --release -p absence-receipt --manifest-path "$REPO/Cargo.toml"
if [ "${1:-}" = verify ]; then verify; exit 0; fi

INDEX="${INDEX:?set INDEX to a crates.io-index checkout at $PIN}"
[ "$(git -C "$INDEX" rev-parse HEAD)" = "$PIN" ] || { echo "INDEX is not at $PIN" >&2; exit 1; }
: > "$WORK/timings.txt"
echo "work dir: $WORK"

leg select   "$AR" select "$INDEX" 100000 "$WORK/manifest.txt"
leg hashes   "$AR" hashes "$INDEX" "$WORK/manifest.txt" "$WORK/documents.tsv"
gunzip -c "$HERE/documents.tsv.gz" | cmp - "$WORK/documents.tsv" && echo "documents.tsv matches the checked-in list"
leg mmr      sh -c "\"$AR\" mmr \"$WORK/documents.tsv\" > \"$WORK/mmr.json\""
leg compile  "$AR" compile "$HERE/policy.txt" "$WORK/absence-table.json"
cmp "$WORK/absence-table.json" "$HERE/absence-table.json" && echo "absence table matches the checked-in table"
(cd "$MT" && lake build dfa-run >/dev/null)
leg dfa-run  sh -c "\"$DFARUN\" \"$HERE/absence-table.json\" --corpus \"$INDEX\" \"$WORK/manifest.txt\" > \"$WORK/dfa-run.json\""
leg rust-count sh -c "\"$AR\" count \"$HERE/absence-table.json\" \"$INDEX\" \"$WORK/manifest.txt\" > \"$WORK/rust-count.json\""
lc=$(sed 's/.*"count":\([0-9]*\).*/\1/' "$WORK/dfa-run.json"); rc=$(sed 's/.*"count":\([0-9]*\).*/\1/' "$WORK/rust-count.json")
[ "$lc" = "$rc" ] || { echo "Lean count $lc != Rust count $rc" >&2; exit 1; }; echo "Lean and Rust counts agree: $lc"
# the PEM control is written here, not checked in (the repository's secret scanner refuses a key header)
printf -- '-----BEGIN OPENSSH %s-----\n' 'PRIVATE KEY' > "$WORK/pem-header.txt"
for c in "$HERE"/controls/*.txt "$WORK/pem-header.txt"; do printf '%s: ' "$(basename "$c")"; "$DFARUN" "$HERE/absence-table.json" "$c"; done
leg emit-record sh -c "cd \"$MT\" && lake env lean --run ../demo/absence-receipt/EmitRecord.lean \"$HERE/absence-table.json\" \"$INDEX/3/c/cxr\" \"$WORK/record-1598.descriptor.json\""
cmp "$WORK/record-1598.descriptor.json" "$HERE/record-1598.descriptor.json" && echo "record descriptor matches the checked-in one"
leg receipt  "$AR" receipt "$HERE/policy.txt" "$HERE/absence-table.json" "$WORK/documents.tsv" "$WORK/dfa-run.json" "$PIN" "$WORK/receipt.json"
if [ -f "$HERE/keys/receipt_ed25519" ]; then
  leg sign ssh-keygen -Y sign -q -f "$HERE/keys/receipt_ed25519" -n absence-receipt "$WORK/receipt.json"
  cp "$WORK/receipt.json" "$WORK/receipt.json.sig" "$WORK/dfa-run.json" "$WORK/mmr.json" "$HERE/"
  gzip -n -c "$WORK/documents.tsv" > "$HERE/documents.tsv.gz"
fi
leg verify verify
cat "$WORK/timings.txt"
