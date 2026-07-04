#!/usr/bin/env bash
# Compile the untrusted IO shell (ffi/mac_io.c) to an object the `orb-mac`
# lean_exe links against. TOML lakefiles cannot compile a C source directly,
# so we precompile here and reference ffi/mac_io.o from `moreLinkArgs` in
# lakefile.toml. Re-run this whenever ffi/mac_io.c changes.
#
# Uses the system C compiler with the Lean toolchain's include path so the
# object matches the runtime ABI (<lean/lean.h>) while still finding the macOS
# SDK system headers (which the bundled `leanc` clang does not locate).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
inc="$(lean --print-prefix)/include"
cc -c -O2 -fPIC -I "$inc" -o "$here/mac_io.o" "$here/mac_io.c"
echo "built $here/mac_io.o"
