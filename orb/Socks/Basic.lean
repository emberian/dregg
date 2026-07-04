/-!
# Upstream proxy egress (SOCKS5 / HTTP CONNECT) — shared vocabulary

This library models the *client* side of upstream proxy chaining: the local
node opens a connection through an upstream proxy and asks it to reach a final
target. Two egress mechanisms are modeled as total deterministic step
functions:

* `Socks.Handshake` — the SOCKS5 client handshake (RFC 1928): method
  negotiation, optional username/password sub-negotiation (RFC 1929), the
  CONNECT request, and the server reply.
* `Socks.HttpTunnel` — the HTTP CONNECT tunnel (RFC 9110 §9.3.6) client:
  `CONNECT host:port` then the status-line reply.
* `Socks.Addr` — the SOCKS5 address field (ATYP + address + port) parser over
  IPv4 / IPv6 / domain, shared by the request and reply.
* `Socks.Relay` — the gated byte relay: application bytes are forwarded only
  once the tunnel is established, and then byte-for-byte in both directions.

Every parser returns the tri-state `Res` (mirroring a sans-IO parser that the
caller retries as more bytes arrive). Byte strings are modeled as lists,
matching the other libraries in this package.
-/

namespace Socks

def version : String := "0.1.0"

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-- Every byte is below 256. -/
theorem u8_toNat_lt (x : UInt8) : x.toNat < 256 := x.toBitVec.isLt

/-- Tri-state parse outcome shared by every parser here. `complete value
consumed` reports the decoded value and the number of leading bytes drained;
`incomplete` asks for more bytes; `error` is an unrecoverable protocol
violation (the connection is closed). This is a *total* classification of the
input: every buffer maps to exactly one constructor. -/
inductive Res (α : Type) where
  | complete (value : α) (consumed : Nat)
  | incomplete
  | error
deriving Repr, DecidableEq

/-- Big-endian `u16` read at `off` (out-of-range bytes read as 0). Used for the
2-byte port field. -/
def readU16 (buf : Bytes) (off : Nat) : Nat :=
  (buf.getD off 0).toNat * 256 + (buf.getD (off + 1) 0).toNat

/-- The egress action a handshake step emits. `wait` is the quiescent /
need-more-bytes non-action; `sendAuth` / `sendConnect` drive the next client
message; `tunnelUp` is the single event that opens the relay gate; `closeErr`
tears the connection down (auth refusal, failure reply, or malformed input). -/
inductive Out where
  | wait
  | sendAuth
  | sendConnect
  | tunnelUp
  | closeErr
deriving Repr, DecidableEq

end Socks
