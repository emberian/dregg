#!/usr/bin/env bash
# Compile the untrusted IO shell (ffi/win_io.c) to an object the `orb-win`
# lean_exe links against. TOML lakefiles cannot compile a C source directly,
# so we precompile here and reference ffi/win_io.o from `moreLinkArgs` in
# lakefile.toml. Re-run this whenever ffi/win_io.c changes.
#
# On a non-Windows host (this mac) win_io.c compiles to its `#else` stub — a
# single `orb_win_serve` that returns an IO error at runtime — which is enough to
# LINK the `orb-win` exe and typecheck IoWin.lean. The real IOCP path is guarded
# by `#ifdef _WIN32` and only compiles under a Windows toolchain (MSVC/clang-cl)
# linked against ws2_32 + mswsock; see WINDOWS-IO-README.md for that build.
#
# Uses the system C compiler with the Lean toolchain's include path so the object
# matches the runtime ABI (<lean/lean.h>) while still finding the host SDK system
# headers (which the bundled `leanc` clang does not locate on macOS).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
inc="$(lean --print-prefix)/include"
cc -c -O2 -fPIC -I "$inc" -o "$here/win_io.o" "$here/win_io.c"
echo "built $here/win_io.o"
