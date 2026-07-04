#!/usr/bin/env bash
# Build the portable AES-GCM fallback static library.
#
# The crypto FFI seam prefers the F*-verified HACL*/EverCrypt AES-GCM, but that
# path is Vale x86-64 assembly and reports UnsupportedAlgorithm where AES-NI+CLMUL
# is absent (ARM, and any non-x86 host). RFC 9001 §5.2 mandates AES-128-GCM for
# QUIC Initial packets, so `ffi/crypto_shim.c` dispatches to this portable backend
# (crates/aes-fallback, over aws-lc-rs / AWS-LC) when the verified path is
# unavailable. It is NOT part of the verified TCB — see CRYPTO-FFI-README.md.
#
# Produces target/release/libaes_fallback.a, which the crypto/socket executables
# link (see lakefile.toml moreLinkArgs). Re-run after editing the crate, then
# `lake build`.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build --release -p aes-fallback
echo "built target/release/libaes_fallback.a (aws-lc-rs AES-GCM fallback)"
