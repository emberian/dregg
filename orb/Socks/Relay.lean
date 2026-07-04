import Socks.Basic

/-!
# The gated byte relay

Once a tunnel is established, the local node relays application bytes between
the client and the upstream target. Two properties are required of that relay,
independent of which handshake (SOCKS5 or HTTP CONNECT) opened it:

* **no-early-egress** (`relay_gated`): while the tunnel is *not* established
  (`up = false`) the relay forwards nothing — the gate is closed.
* **byte-transparency** (`relay_transparent`, `relay_concat`,
  `relay_dir_indep`): once established (`up = true`) the relay is the identity
  on the payload, in both directions, and commutes with re-chunking (the byte
  stream is preserved across arbitrary buffer boundaries).

The relay is parameterized by a single boolean gate `up`, so both handshakes
reuse it: each supplies its own `up` predicate over its phase.
-/

namespace Socks

/-- Relay direction: client→server or server→client. The relay treats both
identically; the parameter exists only to state direction-independence. -/
inductive Dir where
  | c2s
  | s2c
deriving DecidableEq, Repr

/-- The gated relay. `up` is the tunnel-established gate. When closed, no bytes
leave; when open, the payload passes through unchanged. -/
def relay (up : Bool) (_dir : Dir) (payload : Bytes) : Bytes :=
  if up then payload else []

/-- **No-early-egress.** A relay whose gate is closed forwards nothing, in
either direction, for any payload. -/
theorem relay_gated (dir : Dir) (p : Bytes) : relay false dir p = [] := rfl

/-- **Byte-transparency.** An open relay is the identity on the payload. -/
theorem relay_transparent (dir : Dir) (p : Bytes) : relay true dir p = p := rfl

/-- The relay output does not depend on direction: forwarding is symmetric. -/
theorem relay_dir_indep (up : Bool) (p : Bytes) :
    relay up Dir.c2s p = relay up Dir.s2c p := rfl

/-- **Byte-transparency across chunk boundaries.** Relaying a payload split into
arbitrary chunks and concatenating the results yields exactly the concatenation
of the original chunks: no byte is dropped, duplicated, or reordered, and chunk
boundaries carry no semantics. -/
theorem relay_concat (dir : Dir) (chunks : List Bytes) :
    (chunks.map (relay true dir)).flatten = chunks.flatten := by
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.flatten_cons, relay_transparent, ih]

end Socks
