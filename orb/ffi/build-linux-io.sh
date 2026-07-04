#!/usr/bin/env bash
# Compile the Linux IO shell (ffi/linux_io.c) to ffi/linux_io.o for the
# `orb-linux` lean_exe to link. A TOML lakefile links a precompiled object via
# moreLinkArgs; this script produces that object with `leanc` so <lean/lean.h>
# and the Lean ABI resolve exactly as the final link expects.
#
# Backends:
#   default            epoll(7)  — no external dependency.
#   ORB_IO_URING=1     io_uring  — requires liburing-dev (-luring at link time;
#                                  add -luring to the exe's moreLinkArgs too).
#
# On a non-Linux host this still compiles: the source falls through to a stub
# `orb_linux_serve` that returns an IO error, so `orb-linux` links and runs
# (and honestly refuses) on macOS for a build-check.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"

# System C compiler with the Lean toolchain's include path (so <lean/lean.h> and
# the runtime ABI resolve) while still finding the host's system headers, which
# the bundled `leanc` clang (-nostdinc) does not locate. Mirrors build-mac-io.sh.
inc="$(lean --print-prefix)/include"

CFLAGS=(-O2 -c -fPIC -I "$inc")
if [[ "${ORB_IO_URING:-0}" == "1" ]]; then
  CFLAGS+=(-DORB_IO_URING)
  echo "build-linux-io: backend = io_uring (add -luring to moreLinkArgs)"
else
  echo "build-linux-io: backend = epoll"
fi

cc "${CFLAGS[@]}" -o "$here/linux_io.o" "$here/linux_io.c"
echo "build-linux-io: wrote $here/linux_io.o"
