#!/usr/bin/env bash
# Compile the chokepoint step's Lean (minidregg Compiler/Blake3.lean, CommitStep.lean,
# CommitBytes.lean) to C with Lean v4.30.0 -- the version of the seL4-built runtime archives
# in ../executor-rootserver/out/exec-sel4 -- and cross-compile the C for aarch64 ELF, as
# ../executor-pd/scripts/cross-compile-closure.sh does for the executor closure.
# Output: out/libchokepoint_lean_elf.a
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
L="${LEAN_SYSROOT:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0}"
MD="${MINIDREGG:-/Users/ember/dev/minidregg}"
CP="${CHOKEPOINT:-/Users/ember/dev/degg-research/experiments/chokepoint-step}"
OUT="$HERE/out"; O="$OUT/olean"; C="$OUT/c"; OBJ="$OUT/obj"
mkdir -p "$O/Compiler" "$C" "$OBJ"
(cd "$MD" && "$L/bin/lean" --root=. -o "$O/Compiler/Blake3.olean" -c "$C/Compiler_Blake3.c" Compiler/Blake3.lean)
(cd "$CP" && LEAN_PATH="$O" "$L/bin/lean" --root=. -o "$O/CommitStep.olean" -c "$C/CommitStep.c" CommitStep.lean)
(cd "$CP" && LEAN_PATH="$O" "$L/bin/lean" --root=. -o "$O/CommitBytes.olean" -c "$C/CommitBytes.c" CommitBytes.lean)
for f in Compiler_Blake3 CommitStep CommitBytes; do
  "$L/bin/clang" --target=aarch64-unknown-none -ffreestanding -O2 -fno-exceptions \
    -isystem "$L/include/clang" -I "$L/include" -c "$C/$f.c" -o "$OBJ/$f.o"
done
rm -f "$OUT/libchokepoint_lean_elf.a"
/opt/homebrew/Cellar/aarch64-unknown-linux-musl/15.2.0/toolchain/bin/aarch64-linux-musl-ar \
  rcs "$OUT/libchokepoint_lean_elf.a" "$OBJ"/*.o
grep -q 'dregg_chokepoint_arrive' "$C/CommitBytes.c"
echo "[chokepoint] out/libchokepoint_lean_elf.a ($(ls "$OBJ" | wc -l | tr -d ' ') objects, Lean $("$L/bin/lean" --version | head -1))"
