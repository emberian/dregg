#!/usr/bin/env bash
# Mutants exist only in this invocation's private temporary directory.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/caveat-air.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
cd "$repo/metatheory"
lake env lean -o .lake/build/lib/lean/Dregg2/Circuit/Emit/BorrowChainEmit.olean Dregg2/Circuit/Emit/BorrowChainEmit.lean
source_file="$repo/metatheory/Dregg2/Circuit/Emit/CaveatAdmissionEmit.lean"
lake env lean -o .lake/build/lib/lean/Dregg2/Circuit/Emit/CaveatAdmissionEmit.olean "$source_file"
python3 - "$source_file" "$scratch" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
out = Path(sys.argv[2])
mutations = {
    "last_row_bypass": (".base (.boundary .first e)", ".base (.gate e)"),
    "final_borrow": ("else if j = 5 then .const 0", "else if j = 5 then .const 1"),
}
for name, (old, new) in mutations.items():
    if source.count(old) != 1:
        raise SystemExit(f"{name}: expected exactly one generator site")
    (out / f"{name}.lean").write_text(source.replace(old, new, 1))
PY
for mutation in last_row_bypass final_borrow; do
    if lake env lean "$scratch/$mutation.lean" >"$scratch/$mutation.log" 2>&1; then
        echo "FAIL: caveat emitter admitted $mutation mutation" >&2
        exit 1
    fi
    if ! rg -q 'CaveatAdmissionEmit.comparison_sound.*depends on (non-kernel )?axioms' "$scratch/$mutation.log" ||
       ! rg -q 'sorryAx' "$scratch/$mutation.log"; then
        cat "$scratch/$mutation.log" >&2
        echo "FAIL: $mutation failed outside its semantic gate" >&2
        exit 1
    fi
    echo "PASS: $mutation refused by comparison_sound"
done
echo 'PASS: caveat emitter and mutation gates'
