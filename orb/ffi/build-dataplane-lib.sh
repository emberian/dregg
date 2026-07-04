#!/usr/bin/env bash
# Build libdrorb.a — the leanc-compiled proven serve as a static archive a
# native host links against.
#
# `lake build Dataplane:static` compiles the `@[export drorb_serve]` module and
# its transitive dependencies to Mach-O objects under .lake/build/ir/**/*.c.o.export.
# This script archives ALL of those objects into a single static library. The
# host linker pulls only the objects reachable from the symbols it references
# (drorb_serve, initialize_Dataplane and their closure) — the same object set the
# `orb-mac` exe links — so unreferenced modules (including the crypto seam, which
# the deployStepIngress path does not touch) are never pulled in.
#
# Re-run after changing Dataplane.lean or any module in its closure, then rebuild
# the Rust dataplane (crates/dataplane). Idempotent.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build Dataplane:static

out=".lake/build/lib/libdrorb.a"
rm -f "$out"
# All compiled Lean module objects (Mach-O, with exported symbols visible).
find .lake/build/ir -name '*.c.o.export' -print0 | xargs -0 ar crs "$out"
echo "built $out ($(find .lake/build/ir -name '*.c.o.export' | wc -l | tr -d ' ') module objects)"
