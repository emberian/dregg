# H2Sound — HPACK decode CORRECTNESS (RFC 7541), successor to the Wf theorems

`H2/Hpack.lean` proves the HPACK header-block decode is **safe**: every view
entry it emits into the arena `Store` is in-bounds
(`decodeHeaderBlock_wf` / `decodeHeaderBlock_entries_inBounds`), so `resolve` is
total and returns exactly `len` bytes, and the main arena is preserved byte for
byte (`decodeHeaderBlock_main`). That is a bounds result. It says nothing about
*which* bytes: a degenerate decoder that appended nothing and registered
empty-but-in-bounds spans (`⟨sidecarBase, 0⟩`) satisfies every one of those
theorems while resolving every decoded name/value to the empty string.

`H2Sound.lean` proves the **correctness** successor for the literal-header-field
-with-incremental-indexing representation (RFC 7541 §6.2.1), non-Huffman (H=0)
literal name and value — the meaning result the goal clause asks for
("each safety claim upgraded to a correctness claim (parse-soundness etc.)").

## What now holds vs. Wf-only

| Property | `H2/Hpack.lean` (before) | `H2Sound.lean` (now) |
|---|---|---|
| Emitted entries in-bounds | ✅ `decodeHeaderBlock_wf` | ✅ (inherited) |
| Decode returns exactly `len` bytes | ✅ `resolve_length` | ✅ (inherited) |
| Main arena preserved | ✅ `decodeHeaderBlock_main` | ✅ (inherited) |
| **Decoded name = encoded name bytes** | ❌ (bounds only) | ✅ `decode_literalInc_sound` |
| **Decoded value = encoded value bytes** | ❌ (bounds only) | ✅ `decode_literalInc_sound` |
| Degenerate empty-span decoder rejected | ❌ (it passes Wf) | ✅ `degenerate_decoder_refuted` |

## The headline theorem

`H2.Hpack.decode_literalInc_sound`:

    encLit name value := 0x40 :: UInt8.ofNat name.length :: (name ++ UInt8.ofNat value.length :: value)

is the wire encoding of an RFC 7541 §6.2.1 literal field with incremental
indexing — first byte `0x40` (pattern `01`, 6-bit index 0 = literal name), then a
raw (H=0) 7-bit-length-prefixed name literal, then a raw 7-bit-length-prefixed
value literal. For `name.length, value.length < 127`, both valid UTF-8, and
`name` not a routed pseudo-header, decoding `encLit name value` into the empty
store:

* **accepts**, yielding exactly one regular field `⟨ne, ve⟩` and **no**
  pseudo-headers (`r.fields = [⟨ne, ve⟩]`, `r.pseudo = {}`);
* **resolves the decoded field to exactly the encoded bytes**:
  `r.store.resolve ne = some name.toArray` and
  `r.store.resolve ve = some value.toArray`.

The decode is a faithful inverse of the literal encoding: the bytes that come out
are, name-byte for name-byte and value-byte for value-byte, the bytes that went
in — not merely spans that happen to be in-bounds.

`degenerate_decoder_refuted` makes the discriminating power explicit: for any
non-empty `name`, `resolve ne = some name.toArray ≠ some #[]`. The empty-span
decoder that `decodeHeaderBlock_wf` cannot catch fails this theorem.

### Proof spine (all against the REAL `H2/Hpack.lean` + `Arena` theories)

1. `resolve_emitSidecar` — the entry `emitSidecar` registers resolves, in the
   store it returns, to exactly the appended bytes (the sidecar analogue of
   `Arena.Parse.resolve_mkEntry_main`). Bridged by two `Array.extract`/append
   lemmas (`extract_append_right`, `extract_append_left_of_le`).
2. `resolve_appendSidecar` / `resolve_pushEntry` — an already-emitted entry keeps
   resolving to the same bytes when the sidecar grows again (so the name entry
   survives the value append).
3. `emitField_field_ok` — a regular-field emit succeeds when the sidecar has room
   and registers name+value entries resolving to exactly `name`, `value`.
4. `decStr7_raw` / `readStr7_raw` — a raw H=0 7-bit string literal decodes to
   exactly its bytes (the Huffman bit is clear, so the axiomatized
   `HuffmanDecoder` is never consulted — the theorem holds for **every** decoder).
5. `decodeLiteralField_lit_sound` → `decodeOneField_literalInc_sound` →
   `decodeBlock_one_field` → `decode_literalInc_sound`.

## Scope — what is UNCLOSED, and why

* **Huffman string literals (H=1).** UNCLOSED. In `H2/Hpack.lean` the Huffman
  decoder is the axiomatized `HuffmanDecoder` interface with no implementation;
  there is nothing to be sound *against*. Every theorem here fixes H=0; the
  decoder is never consulted, so the results hold uniformly over every Huffman
  -decoder behavior. Closing H=1 requires first *implementing* the RFC 7541
  Appendix B canonical Huffman code and proving it inverts the encoder — a
  separate build.
* **Indexed representations (§6.1) and static-name references (§6.2.1 with
  `idx ≠ 0`).** Not covered here. These resolve names/values out of the modeled
  static table; their correctness is table-lookup correctness, a different (and
  smaller) obligation than literal round-trip. The literal path — where the bytes
  are genuinely carried on the wire — is the real correctness core.
* **The dynamic table (§2.3/§6.2.1 insertion, §6.3 size update).** Remains the
  explicit out-of-scope stub of `H2/Hpack.lean` (no table state exists). §6.2.1's
  "incremental indexing" *insertion* side effect is a documented no-op in the
  model; the store-emit the decode performs IS the insertion this model realizes,
  and `decode_literalInc_sound` proves that emit is byte-faithful. A real dynamic
  table would need its own state model and eviction correctness.
* **Multi-field blocks.** `decode_literalInc_sound` is stated for a single-field
  block. The per-field emit lemmas (`emitField_field_ok`,
  `decodeOneField_literalInc_sound`) are field-local; extending to an n-field
  block is an induction over `decodeBlock` (the loop-preservation shape already
  used by `decodeBlock_wf`), left for a follow-up.

## QPACK (HTTP/3) — the same upgrade, `QpackSound.lean`

`H3/Qpack.lean` had the same `Wf`-only status. `QpackSound.lean` closes the
correctness successor for the RFC 9204 §4.5.6 representation — a literal field
line with a **literal name** and literal value, non-Huffman:

    encQLit name value := 0x00 :: 0x00 :: UInt8.ofNat (0x20 + name.length) :: (name ++ UInt8.ofNat value.length :: value)

(the `00 00` is the no-dynamic-reference section prefix: encoded Required Insert
Count 0, Delta Base 0). `H3.Qpack.decodeQ_literalName_sound`: for
`name.length < 7` (the 3-bit name-length prefix), `value.length < 127`, both
valid UTF-8, `name` not a routed pseudo-header — decoding into the empty store
accepts, yields exactly one regular field `⟨ne, ve⟩` and no pseudo-headers, and
`resolve ne = some name.toArray`, `resolve ve = some value.toArray`. Same scope
cuts as HPACK (Huffman UNCLOSED, static/dynamic references and multi-line
sections out of scope). The Arena-level `resolve`/append lemmas are re-proved in
`QpackSound.lean` (identical to the H2Sound ones) because `H3.Qpack` carries its
own emit primitive.

## Verification

    lake env lean H2Sound.lean      # elaborates clean against the built Arena / H2.Hpack oleans
    lake env lean QpackSound.lean   # ditto against Arena / H3.Qpack

* Zero `sorry`, zero `admit`, no `native_decide` (in either file).
* `#print axioms` for `H2.Hpack.decode_literalInc_sound`,
  `decodeOneField_literalInc_sound`, `degenerate_decoder_refuted`,
  `resolve_emitSidecar`, and `H3.Qpack.decodeQ_literalName_sound`,
  `decodeOneLine_literalName_sound`:
  `[propext, Classical.choice, Quot.sound]` — the sacred subset, nothing else.

To make them first-class `lake build` targets, add (mirroring `ArenaSound` /
`HeaderSound`) the stanzas below to `lakefile.toml`. They are intentionally NOT
added here to keep the shared lakefile swarm-safe:

    [[lean_lib]]
    name = "H2Sound"
    srcDir = "."
    roots = ["H2Sound"]

    [[lean_lib]]
    name = "QpackSound"
    srcDir = "."
    roots = ["QpackSound"]
