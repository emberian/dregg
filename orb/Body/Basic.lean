/-!
# Body — shared vocabulary

Shared definitions for the `Body` library: the byte-string type and the two
framing octets (CR, LF) that HTTP/1.1 message framing is built from.

The library models request/response body transfer over a byte stream in two
framings and one streaming reader per framing:

* `Body.ContentLength` — a fixed total (`Content-Length`): read exactly `N`
  bytes. The reader folds input segments into a delivered prefix; a complete
  read delivers exactly the length-`N` prefix of the input, in order, and never
  overshoots into a following message.
* `Body.Hex` — the hexadecimal chunk-size codec (RFC 7230 §4.1 `chunk-size`):
  `toHex` / `parseHex` with a proven round trip, and the fact that hex digits
  never collide with the CR/LF framing octets.
* `Body.Chunked` — chunked transfer-encoding (RFC 7230 §4.1): the chunk-header
  parse (total, consumed-monotone), a single-frame decoder, and a streaming
  decode that recovers exactly the concatenation of the chunk payloads with no
  framing octet leaking into the body.

Byte strings are modeled as lists, matching the other libraries in this
package.
-/

namespace Body

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-- ASCII carriage return (`0x0D`). -/
def CR : UInt8 := 13
/-- ASCII line feed (`0x0A`). -/
def LF : UInt8 := 10

def version : String := "0.1.0"

end Body
