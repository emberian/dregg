# Compression — DEFLATE inflate + gzip (RFC 1951 / 1952)

A total, output-bounded model of DEFLATE decompression and the gzip container,
verified in Lean 4 (core only). Two single-file libraries:

- `Deflate.lean` — DEFLATE inflate (RFC 1951), the algorithm a server runs on a
  compressed request body / header block.
- `Gzip.lean` — the gzip container (RFC 1952) over `Deflate`: magic, header,
  CRC-32 + ISIZE trailer, `gunzip`.

Both derive from the RFCs, not from any implementation. The headline property is
the **decompression-bomb bound**: a tiny compressed input cannot force an
unbounded output. Decompression (inflate) is the dangerous direction — a server
*receives* compressed data and must expand it — so the model focuses there and
makes the memory bound a theorem.

## Why this is the interesting direction

DEFLATE/gzip sits under `Content-Encoding: gzip`, zlib, PNG, HTTP/2 HPACK-adjacent
paths, and TLS certificate compression. A compressed stream can *name* an
enormous output in very few bytes (the classic "zip bomb"): the LZ77 back-
reference and the run-length code-length repeats both let O(1) input describe O(n)
output. The safety question is not "is the output correct" but "can the output
size be forced past what the caller budgeted." Here it cannot: the answer is a
theorem, `inflate_output_bounded` / `gunzip_output_bounded`.

## `Deflate.lean`

### The model (all from RFC 1951)

- **Bit stream** (§3.1.1): DEFLATE packs bits LSB-first within a byte; Huffman
  codewords are packed MSB-first. `byteBits` / `bytesToBits` flatten bytes to a
  `List Bool` in that order; `takeBitsLE n` reads an `n`-bit LSB-first integer
  (block header, lengths, extra bits); the Huffman `decode` assembles code bits
  MSB-first.
- **Block types** (§3.2.3): stored (`00`), fixed-Huffman (`01`),
  dynamic-Huffman (`10`); `11` is the reserved error.
- **Stored blocks** (§3.2.4): `align` to the next byte boundary, read `LEN` and
  its one's-complement `NLEN`, copy `LEN` literal bytes.
- **Canonical Huffman** (§3.2.2): `buildHuffman` turns a per-symbol code-length
  list into the canonical code assignment (`firstCode` / `symCode`); `decode`
  reads bits until a codeword matches.
- **Fixed Huffman** (§3.2.6): the fixed literal/length and distance code lengths,
  through the same `buildHuffman`.
- **Dynamic Huffman** (§3.2.7): `HLIT`/`HDIST`/`HCLEN`, the `16,17,18,0,8,…`
  code-length permutation, the run-length repeat codes (16/17/18), the two trees.
- **LZ77 back-references** (§3.2.5): length codes 257–285 and distance codes 0–29
  with their extra-bit tables; `copyMatch` copies from earlier output one byte at
  a time so overlap (length > distance) is handled.

`inflate` is a `def` on explicit fuel (not `partial def`): it terminates on all
input. A malformed stream — a nonexistent codeword, a distance past the start of
output, a bad `NLEN`, a reserved block type, a short read — returns a typed `Err`,
never diverges.

### Theorems

| theorem | statement |
|---|---|
| `inflate_output_bounded` | `∀ cfg input, (inflate cfg input).out.size ≤ cfg.maxOut` — the decompression-bomb bound, for **every** input. |
| `inflate_total` | `inflate` returns a `Result` for every input (it is a total `def`). |
| `inflate_stored_identity` | For `x.length < 65536` and `x.length ≤ cfg.maxOut`: `inflate cfg (deflateStored x)` returns exactly `x`, no error — the reader inverts the writer on the stored path. |
| `inflate_fixed_roundtrip_empty` | `inflate (deflateFixed []) = []` — the fixed-Huffman path, empty message. |
| `inflate_fixed_roundtrip_hi` | `inflate (deflateFixed [0x68,0x69]) = [0x68,0x69]` — a concrete fixed-Huffman round-trip, kernel-checked through `buildHuffman fixedLitLengths` and the MSB-first Huffman `decode`. |

The bound is proved compositionally: every byte reaching the output passes one of
`copyMatch`, `pushBounded`, or the literal push in `bodyStep`, each of which
refuses to append once `out.size = maxOut`. Lemmas `copyMatch_le`,
`pushBounded_le`, `bodyStep_le`, `decodeBody_le`, `inflateStored_le`,
`inflateAux_le` lift that one-step guard through the whole pipeline.

The stored identity is the "reader inverts writer" round-trip. Its spine is a
bit-level inversion proof: `takeBitsLE_bitsN` (reading `k` LSB-first bits recovers
`n % 2^k`, by induction peeling one bit and `Nat.mod_mul`), `byteBits_take` (8
bits recover a byte), `takeBytes_bytesToBits` (byte reads invert `bytesToBits`),
`u16le_read` (a 16-bit little-endian field), and `pushBounded_all` (below the
ceiling the whole literal payload is appended). These thread through `align`
(dropping exactly the 5 pad bits), the `LEN`/`NLEN` reads, the `NLEN = ~LEN`
check, the literal copy, and the `BFINAL=1` block-driver exit.

The fixed-Huffman round-trips use a small total encoder (`deflateFixed`, with
`msbBits` / `packBytes` on explicit fuel so it reduces in the kernel) and are
closed by `rfl` — genuine computation through the fixed trees, not an axiom.

## `Gzip.lean`

### The model (RFC 1952)

- **CRC-32** (§8): the reflected `0xEDB88320` variant, a real total function
  (`crc32Round` → `crc32Byte` → `crc32`). Validated against `zlib.crc32`:
  `crc32 [] = 0`, `crc32 "hi" = 0xD8932AAC`, `crc32 "hello world" = 0x0D4A1185`.
- **Header** (§2.3): the 10 fixed bytes (`ID1 ID2 CM FLG`, `MTIME`×4, `XFL`,
  `OS`), then the FLG-selected optional fields — FEXTRA / FNAME / FCOMMENT /
  FHCRC — which `parseHeader` skips (fuel-bounded, total).
- **Trailer** (§2.3.1): `CRC32` ‖ `ISIZE`, both little-endian 32-bit. Modelled as
  a whole buffer: the last 8 bytes are the trailer, the middle is the DEFLATE
  payload.
- **`gunzip`**: parse header → split payload/trailer → `Deflate.inflate` under the
  ceiling → verify CRC-32 and ISIZE. On any failure the output is `#[]` (nothing
  is handed back); on success it is exactly the inflated, checked bytes.

### Theorems

| theorem | statement |
|---|---|
| `gzip_header_wellformed` | `parseHeader (mkHeader ++ rest) = some (⟨0x1f,0x8b,0x08,0x00⟩, rest)` — a well-formed header parses back, exposing the RFC 1952 magic and DEFLATE method. |
| `gunzip_output_bounded` | `∀ cfg input, (gunzip cfg input).out.size ≤ cfg.maxOut` — the bomb bound, composed from `Deflate.inflate_output_bounded` (the only non-empty output comes from `inflate`; every failure path returns `#[]`). |
| `gzip_accepts_valid` | `gunzip (gzipStored [0x68,0x69])` returns `[0x68,0x69]`, no error — a valid container round-trips (header parses, stored block inflates, CRC + size match). |
| `gzip_crc_checked` | corrupting the trailer CRC-32 makes `gunzip` fail with `crcMismatch` — a wrong CRC is **rejected**, never accepted. |

### CRC-32 is a checksum, not a MAC

The trailer CRC-32 detects accidental corruption; it is *not* cryptographic
integrity. An attacker who controls the payload recomputes the CRC. Authenticity
lives in the AEAD/signature boundary (`Crypto` / `TlsCrypto`, over
HACL*/EverCrypt), not here. `gzip_crc_checked` is the right claim — corruption is
caught — and no stronger claim is made.

## Verification

Single-file check (Deflate imports nothing; Gzip imports Deflate, so build the
lib first):

```
lake build Deflate
lake env lean Deflate.lean          # ⇒ exit 0, no output
lake build Gzip
lake env lean Gzip.lean             # ⇒ exit 0, no output
```

Axiom footprint — every theorem stays within `{propext, Quot.sound,
Classical.choice}`; no `sorry`, no `native_decide` (`Lean.ofReduceBool` would
escape the set), no unclosed goals:

```
#print axioms Deflate.inflate_output_bounded     -- [propext, Quot.sound]
#print axioms Deflate.inflate_stored_identity    -- [propext, Classical.choice, Quot.sound]
#print axioms Deflate.inflate_fixed_roundtrip_hi -- [propext]
#print axioms Gzip.gunzip_output_bounded         -- [propext, Quot.sound]
#print axioms Gzip.gzip_crc_checked              -- [propext, Quot.sound]
```

## Scope / non-goals

- Inflate holds the whole output in the bounded array (no windowed / streaming
  operation, no preset dictionary). The bound is on total output size, which is
  the bomb-relevant quantity.
- Deflate *compression* (the encoder) is modelled only as far as the round-trip
  witnesses need (`deflateStored`, `deflateFixed`); the server side is inflate.
- zlib framing (RFC 1950) is not modelled; gzip (RFC 1952) is.
- The gzip container is a whole buffer, not a byte-exact streaming deframer.
