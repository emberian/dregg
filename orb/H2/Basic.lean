/-!
# H2 — HTTP/2 framing, HPACK arena decode, and the per-stream FSM

Shared vocabulary for the H2 library:

* the frame layer (`H2/Frame.lean`) — the common 9-octet frame header
  (RFC 9113 §4.1: length/type/flags/`R`+stream-id, the reserved-bit mask),
  the frame taxonomy (§6), unknown-type handling (§4.1), and the decoder's
  totality / consumed-monotonicity / frame-size-limit theorems.
* `H2.Hpack` — HPACK (RFC 7541) prefix integers, string literals, and the
  static-table subset, decoding *into* the two-arena `Arena.Store` through one
  audited emit primitive; the headline theorem is well-formedness preservation
  (every emitted view entry is in-bounds of the arena it addresses), proven
  statically over every Huffman-decoder behavior.
* `H2.Stream` — the per-stream state machine (RFC 9113 §5.1 / RFC 7540 §5.1)
  as a total deterministic step; closed is absorbing and no DATA is delivered
  to a stream whose remote half is closed.

Byte strings are modeled as lists for ease of reasoning, matching the other
libraries in this package.
-/

namespace H2

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

def version : String := "0.1.0"

end H2
