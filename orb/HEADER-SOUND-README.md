# Header-block soundness — what now holds vs safety-only

`HeaderSound.lean` upgrades the header fields of the HTTP/1.1 head parser from a
**safety** guarantee to a **correctness** (parse-soundness) guarantee, mirroring
what `ArenaSound.lean` did for the request line.

Toolchain: Lean 4 v4.17.0. Verify with `lake build HeaderSound`; the file has
**zero `sorry`** and its axiom footprint is `{propext, Quot.sound,
Classical.choice}` (checked with `#print axioms parse_headers_sound`).

## The gap this closes

`parse_wf` (`Arena/ParseTheorems.lean`) is a SAFETY result. For a `complete`
parse it proves every registered header view range — the wire ranges in the main
arena and the synthesized canonical names in the sidecar — is in-bounds, so
`resolve` is total and returns exactly `len` bytes. But bounds say nothing about
*which* bytes. A degenerate parser that registered empty-but-in-bounds header
spans (every name/value `⟨0,0⟩`) satisfies `parse_wf` while resolving every
header field to the empty string. Safety, not meaning.

## What is now PROVEN (the correctness core)

For a `complete` parse, `parse_headers_sound` produces the header-line spans in
one-to-one correspondence with `req.headers` (relation `HeadersSound`, a local
`Forall₂` — that constant is not in this core toolchain), and every header
satisfies `HeaderFieldSound input req.store sp ph`:

1. **Name/value split is at the right byte.** The header line `L = sliceSpan
   input sp` has a `:` at offset `ci`, `ci` is the FIRST `:` (`∀ j < ci,
   L[j] ≠ ':'`), and the name is non-empty (`0 < ci`). This is the RFC 9112
   `field-name ":" OWS field-value OWS` split, located exactly.

2. **Value = its exact OWS-trimmed input substring.** The value entry resolves
   (`req.store.resolve ph.value = some vb`) and `vb.toList` is *byte-for-byte*
   the value region of the line with leading and trailing SP/HTAB stripped:
   `((L.drop (ci+1)).drop lead).take (… − trail)`, where `lead`/`trail` are the
   leading/trailing OWS run lengths.

3. **Name = its exact lowercased pre-colon bytes.** The name entry resolves and
   `nb.toList = (L.take ci).map lowerByte`. This covers BOTH canonical-name
   representations the parser uses:
   * an already-lowercase name points into the **main arena** and resolves to the
     name bytes themselves (which equal their own lowercasing —
     `map_lowerByte_id`);
   * a mixed-case name resolves out of the **sidecar** to the lowercased bytes the
     canonicalization synthesized there. The sidecar bridge
     (`resolve_mkEntry_sidecar` + `prefix_drop_take`) is the load-bearing new
     piece: a canonical name written at the current sidecar end survives every
     later append (the sidecar only grows to the right — `parseHeaders_prefix`),
     so it still resolves to the bytes that were written when resolved against the
     FINAL sidecar.

The **degenerate empty-span parser FAILS this**: an empty name span forces
`ci = 0` (no room for a name byte), contradicting `0 < ci` and `L[ci] = ':'`.
Soundness, not just type-checking.

### Recipe followed (per the ArenaSound pattern)

* `resolve_mkEntry_main_toList` (reused from ArenaSound) + `resolve_mkEntry_sidecar_toList`
  (new): the `resolve`→concrete-substring bridges for the two arenas.
* `parseHeaderLine_sound`: the per-line field-extraction lemma (first-`:`,
  non-empty name, OWS-trimmed value) — the pure analogue of
  `parseRequestLine_sound`.
* `sliceSpan_drop` / `prefix_drop_take`: the slice arithmetic connecting the line
  the parser sees back to concrete input / sidecar offsets.
* `parseHeaders_sound`: threads the above over the whole header list, resolving
  every entry against the final store.

### Theorem index

| name | statement |
|------|-----------|
| `parse_headers_sound` | top-level: every header of a `complete` parse is `HeaderFieldSound` |
| `parseHeaders_sound` | the threaded induction over the header spans |
| `parseHeaderLine_sound` | per-line: spans denote the exact grammar fields |
| `resolve_mkEntry_sidecar[_toList]` | sidecar `resolve` = concrete slice |
| `prefix_drop_take` | a prefix knows its own slice (sidecar survival) |
| `map_lowerByte_id` | lowercasing is identity on an already-lowercase span |

## What is UNCLOSED (named honestly)

* **Full header-BLOCK re-serialization.** ArenaSound closes the request-line
  round-trip (`reconstruct_two_sep`: `method ++ " " ++ target ++ " " ++ version
  = input.take L`). The header-block analogue — concatenating every reconstructed
  `name ":" OWS value OWS` line with its CRLF separators back into the exact input
  head region — is NOT proven. It ranges over an arbitrary number of lines each
  carrying its own (unrecovered) original OWS, so the per-field extraction above
  does not by itself rebuild the exact original bytes of each line. This is the
  real remaining work for a byte-exact header-block round-trip; the per-header
  field-extraction correctness proven here is the soundness core the goal clause
  ("each safety claim upgraded to a correctness claim (parse-soundness etc.)")
  asks for.

* **HPACK / QPACK decode-correctness.** HTTP/2 and HTTP/3 header compression are
  SEPARATE codecs (dynamic-table state machines), not this HTTP/1.1 head parser,
  and are entirely out of scope here.

## Safety-only vs correctness, at a glance

| header property | before (safety) | now (correctness) |
|---|---|---|
| value range in-bounds, `resolve` total | `parse_wf` | (still) |
| value = exact OWS-trimmed input substring | — | `parse_headers_sound` |
| name range in-bounds (main or sidecar) | `parse_wf` | (still) |
| name = exact lowercased pre-colon input bytes | — | `parse_headers_sound` |
| first-`:` split, non-empty name | — | `parse_headers_sound` |
| full header-block byte-exact re-serialization | — | UNCLOSED |
