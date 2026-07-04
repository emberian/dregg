/-!
# H3 — HTTP/3 framing and QPACK field-section decoding

Shared vocabulary for the H3 library:

* `H3.Varint` — QUIC variable-length integers (RFC 9000 §16), with round-trip,
  length-bound, and canonical-form theorems.
* the frame layer (`H3/Frame.lean`) — HTTP/3 frames (RFC 9114 §7.2): the
  type + length varint header, the frame taxonomy, the unknown-type skip
  rule, and consumed-monotonicity.
* `H3.Qpack` — QPACK (RFC 9204) prefix integers, string literals, and the
  static-table subset, decoding *into* the two-arena `Arena.Store`; the
  headline theorem is well-formedness preservation (every emitted view entry
  is in-bounds of the arena it addresses).

Byte strings are modeled as lists for ease of reasoning, matching the other
libraries in this package.
-/

namespace H3

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

def version : String := "0.1.0"

end H3
