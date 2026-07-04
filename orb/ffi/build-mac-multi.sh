#!/usr/bin/env bash
# Compile the two untrusted IO shells the `orb-mac-multi` exe links against:
#   ffi/mac_io.c  -> ffi/mac_io.o   (TCP: HTTP/1.1 + h2c + the WebSocket lane)
#   ffi/mac_udp.c -> ffi/mac_udp.o  (UDP: the QUIC/HTTP-3 datagram lane)
# TOML lakefiles cannot compile a C source directly, so we precompile here and
# reference the objects from moreLinkArgs in lakefile.toml. Re-run whenever
# either C source changes.
#
# Uses the system C compiler with the Lean toolchain's include path so the
# objects match the runtime ABI (<lean/lean.h>) while still finding the macOS
# SDK system headers (which the bundled leanc clang does not locate).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
inc="$(lean --print-prefix)/include"
cc -c -O2 -fPIC -I "$inc" -o "$here/mac_io.o"  "$here/mac_io.c"
cc -c -O2 -fPIC -I "$inc" -o "$here/mac_udp.o" "$here/mac_udp.c"
echo "built $here/mac_io.o and $here/mac_udp.o"
