#!/usr/bin/env bash
# Compile the crypto FFI shim to an object file that the `crypto-selftest`
# lean_exe links via moreLinkArgs. TOML lakefiles cannot compile a C source as a
# build target, so this runs as a prerequisite step. Idempotent; re-run after
# editing crypto_shim.c, then `lake build crypto-selftest`.
#
# The shim calls HACL*/EverCrypt (Project Everest), the F*-verified crypto
# extracted to C by KaRaMeL. It compiles against the extracted headers in
# $HACL_DIST and the KaRaMeL runtime headers in $KRML/include, and the
# executable links the prebuilt libevercrypt.a. Build that archive once with:
#     cd $HACL_DIST && ./configure && make -j libevercrypt.a
set -euo pipefail
cd "$(dirname "$0")/.."

# Resolve the active toolchain's include dir (lean/lean.h) robustly:
TOOLCHAIN_INC="$(lean --print-prefix 2>/dev/null || true)/include"
if [ ! -f "$TOOLCHAIN_INC/lean/lean.h" ]; then
  TOOLCHAIN_INC="$HOME/.elan/toolchains/leanprover--lean4---v4.17.0/include"
fi

# HACL*/EverCrypt extracted C + KaRaMeL runtime headers.
HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
KRML="${KRML:-$HOME/src/hacl-star/dist/karamel}"

if [ ! -f "$HACL_DIST/EverCrypt_AEAD.h" ]; then
  echo "error: EverCrypt headers not found under HACL_DIST=$HACL_DIST" >&2
  exit 1
fi
if [ ! -f "$HACL_DIST/libevercrypt.a" ]; then
  echo "note: $HACL_DIST/libevercrypt.a missing — building it" >&2
  ( cd "$HACL_DIST" && ./configure && make -j libevercrypt.a )
fi

cc -O2 -fPIC \
   -I"$TOOLCHAIN_INC" \
   -I"$HACL_DIST" \
   -I"$KRML/include" \
   -I"$KRML/krmllib/dist/minimal" \
   -c ffi/crypto_shim.c \
   -o ffi/crypto_shim.o

echo "built ffi/crypto_shim.o (HACL*/EverCrypt backend)"
