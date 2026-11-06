#!/usr/bin/env bash
# The only mutations are in this invocation's temporary directory.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/deco-air.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
source_file="$repo/metatheory/Dregg2/Circuit/Emit/DecoLeafEmit.lean"
cd "$repo/metatheory"
lake env lean Dregg2/Circuit/Emit/BoundedFactEmit.lean
lake env lean "$source_file"
python3 - "$source_file" "$scratch" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
out = Path(sys.argv[2])
mutations = {
    "last_row_bypass": (".base (.boundary .first e)", ".base (.gate e)"),
    "identity_wrong_input": ("![.var 5, .var 3, .const 0, .const 0, .const 0]",
                             "![.var 5, .var 4, .const 0, .const 0, .const 0]"),
}
for name, (old, new) in mutations.items():
    if source.count(old) != 1:
        raise SystemExit(f"{name}: expected exactly one generator site")
    (out / f"{name}.lean").write_text(source.replace(old, new, 1))
PY
for mutation in last_row_bypass identity_wrong_input; do
  if lake env lean "$scratch/$mutation.lean" >"$scratch/$mutation.log" 2>&1; then
    echo "FAIL: DECO emitter admitted $mutation mutation" >&2
    exit 1
  fi
  theorem=amount_range
  if [[ "$mutation" == identity_wrong_input ]]; then theorem=payment_identity; fi
  if ! rg -q "DecoLeafEmit\.$theorem.*depends on axioms" "$scratch/$mutation.log" ||
     ! rg -q 'sorryAx' "$scratch/$mutation.log"; then
    cat "$scratch/$mutation.log" >&2
    echo "FAIL: $mutation failed outside its semantic gate" >&2
    exit 1
  fi
  echo "PASS: $mutation refused by $theorem"
done
echo 'PASS: DECO emitter and mutation gates'
