# WireGuard / DERP / DISCO — the mesh stack on real crypto

Three sans-IO transition-system models, verified in Lean 4 (v4.17.0,
core-only), covering the peer-to-peer mesh stack:

| file            | protocol                                   | crypto                         |
|-----------------|--------------------------------------------|--------------------------------|
| `Wireguard.lean`| WireGuard: Noise IK handshake + data plane | **real** (`Crypto`)            |
| `Derp.lean`     | DERP relay framing + mesh presence         | boundary (relay is opaque)     |
| `Disco.lean`    | DISCO NAT-traversal path selection         | boundary (NaCl box — abstract) |

Verify (single-file):

```
lake env lean Derp.lean
lake env lean Disco.lean
lake build Wireguard          # imports Crypto ⇒ multi-file
```

Axiom footprint of every theorem below: `propext`, `Quot.sound` — plus,
for the WireGuard `Noise` theorems only, the named
`Crypto.Assumptions.*` primitives (the discharged-upstream HACL*/EverCrypt
trust boundary). No `Classical.choice`, no `sorry`.

---

## Wireguard.lean

### The handshake is real crypto, not an uninterpreted `deriveKeys`

The transport FSM keeps crypto abstract so its safety theorems
are cipher-independent. The `Noise` section fills that boundary in with
the actual Noise IKpsk2 key schedule, computed on the verified primitives
`Crypto` exposes:

* **X25519** (`Crypto.x25519`, `Crypto.x25519Base`) — the four
  Diffie–Hellman shared secrets `es, ss, ee, se`.
* **HKDF-SHA-256** (`Crypto.hkdfExtract` / `Crypto.hkdfExpand`) — the
  chaining-key ratchet, the whitepaper's `KDF_n` (`Noise.kdf`).
* **ChaCha20-Poly1305** (`Crypto.chachaSeal` / `Crypto.chachaOpen`) — the
  AEAD-sealed static key and timestamp of the initiation.

The message layout follows the WireGuard whitepaper (Donenfeld, *WireGuard:
Next Generation Kernel Network Tunnel*) §5.4 exactly, with one honest
substitution: the paper mandates BLAKE2s, and the verified seam offers
SHA-256, so the ratchet runs on SHA-256. The key-agreement argument is
identical under either hash — it turns only on the X25519 DH relation, not
on the hash.

**`wg_handshake_real`** — the load-bearing theorem. Given well-formed
keypairs (`x25519Base priv = some pub` for each), the initiator and
responder — each computing its four DH secrets from the opposite end —
derive the *same* chaining key. Each of the four steps discharges

```
x25519 a (x25519Base b)  =  x25519 b (x25519Base a)
```

by `Crypto.Assumptions.x25519_dh_agree`; the ratchet is otherwise a
deterministic fold over identical public inputs, so the results coincide.

Corollaries:

* **`wg_transport_keys_agree`** — the 64-byte `KDF2(ck, ε)` transport
  material is identical on both ends, so initiator-send = responder-recv
  and vice versa.
* **`wg_static_key_authenticated`** — the responder, with the derived key
  and transcript, opens `encrypted_static` to *exactly* the initiator's
  static public key (real AEAD roundtrip, via `chacha_open_seal_roundtrip`).
* **`wg_static_key_unforgeable`** — the only ciphertext that opens is the
  one the genuine initiator sealed (`chacha_open_authentic`): AEAD
  forgery-resistance, so a responder that admits only on
  `chachaOpen … = some spubI` never admits a peer without the key material.

### The sliding replay window, fully characterized

Rejection is proved by `Window.replay_rejected` and
`Window.too_old_rejected`; the other direction and the full `iff` complete
the characterization:

* **`wg_window_accepts_ahead`** — a counter at/beyond the high-water mark
  is always accepted (nothing ahead of the window can be a replay).
* **`wg_window_accepts_fresh`** — a counter inside the window that has not
  been seen is accepted (legitimate reordering is not mistaken for replay).
* **`wg_replay_window_correct`** — the complete decision: `willAccept c`
  iff `c` is ahead of the window **or** (inside the window **and** unseen).
  With the window invariant this is the full anti-replay statement:
  accepted ⇔ in-window-and-unseen (or ahead).

The FSM-level `wg_replay_rejected` / `wg_counter_monotone` are also present.

### Rekey timers (§6.1)

`Rekey` carries the stock constants — `REKEY_AFTER_MESSAGES = 2^60`,
`REJECT_AFTER_MESSAGES = 2^64 − 2^13 − 1`, `REKEY_AFTER_TIME = 120 s`,
`REJECT_AFTER_TIME = 180 s`, `REKEY_TIMEOUT = 5 s` — over a `Session`
(messages sent, age).

* **`wg_rekey_before_reject`** — any session that has reached a hard reject
  threshold has already crossed the soft rekey threshold. A correct peer
  always starts a fresh handshake before it is ever forced to drop the
  session, so a live tunnel never stalls for want of a key.

### Cookie-reply DoS mitigation (§5.3 / §5.4.7)

`Cookie.admit mac1Valid mac2Valid underLoad : Reply` is the responder's
admission decision. MAC1 is always required; under load a valid MAC2
(derived from a recent cookie tied to the source address) is additionally
required, else the responder answers with a cheap cookie reply and does
**no** X25519/AEAD work.

* **`wg_cookie_mitigates`** — under load, an initiation without a valid
  cookie MAC2 is never admitted to the handshake (`admit _ false true ≠
  handshake`). An off-path flood cannot force handshake computation.
* Supporting: `wg_cookie_reply_under_load`, `wg_cookie_admits_valid`,
  `wg_cookie_bad_mac1_dropped`.

The cookie's own authenticity (a keyed MAC over the source address under a
rotating secret) remains the named crypto boundary.

---

## Derp.lean

The relay wire framing is proven by `derp_frame_bounds`,
`derp_no_overread`, `derp_parse_serialize`, and the keyed-payload splits. Also:

* **`derp_type_roundtrip_named`** — every one of the sixteen assigned frame
  types round-trips its wire tag (`ofByte (toByte ft) = ft`).
* **Keepalive** — `keepAliveFrame` (type `0x06`, empty payload) and
  **`derp_keepalive_roundtrip`**: it serializes/parses as a well-formed
  zero-length frame, not a truncation.
* **Mesh presence** — `Presence` folds inbound relay frames into the set of
  peers the relay announces as reachable:
  * **`derp_peer_present_adds`** — a peerPresent makes a peer present;
  * **`derp_peer_gone_removes`** — a peerGone removes every copy of it;
  * **`derp_keepalive_presence`** — a keepAlive refreshes liveness without
    changing membership.
* **Streaming** — `parseFrames` parses a whole buffer into every complete
  frame (well-founded on buffer length, since each frame consumes ≥ 5
  header bytes), and **`derp_parseFrames_bounded`** proves every emitted
  frame respects the cap — the streamed parser never over-reads.

The relay treats packet payloads as opaque, which is faithful: DERP's
end-to-end encryption is invisible to the relay, so no crypto is needed here.

---

## Disco.lean

The probing FSM (unprobed → probed → verified, `disco_no_promote_without_pong`,
`disco_verified_needs_pong`, `disco_verified_sticky`) is proven. The full
path-selection layer:

* **`disco_bestVerified_min`** — endpoint priority is a genuine minimum:
  the selected direct endpoint's latency is ≤ that of *any* verified
  endpoint, so selection is by lowest measured RTT, not first match.
  (Helper: `bestVerified_none_no_verified`.)
* **`selectPath`** — a direct verified endpoint if one exists, otherwise
  the DERP relay (`PathKind.direct` / `.derp`):
  * **`disco_direct_preferred`** — whenever any endpoint is verified,
    selection returns a *direct* path, never the relay;
  * **`disco_relay_fallback`** — with no verified endpoint, it relays;
  * **`disco_direct_is_verified`** — a direct selection is always a
    verified endpoint;
  * **`disco_derp_to_direct_upgrade`** — if before a step no endpoint is
    verified (the node relays) and after it one is (a pong landed), then
    selection upgrades from the DERP relay to a direct path. This is the
    point of the discipline: relay first, promote to direct once proven.

DISCO's Ping/Pong authenticity is a NaCl box (Curve25519 + XSalsa20 +
Poly1305), which is outside the primitive set the verified `Crypto` seam
exposes; it therefore stays the named `Config.authPong` boundary, and the
TxID unguessability that makes a spoofed pong impossible is the security
assumption behind it. The path-selection theorems above are independent of
that boundary.

---

## What is real vs. what is boundary

Real (computed on verified HACL*/EverCrypt primitives, agreement/roundtrip
proven): the WireGuard Noise IK chaining-key ratchet, the X25519 DH chain,
transport-key agreement, and the AEAD-sealed static key.

Named boundary (assumed, honestly): X25519 hardness and AEAD IND-CPA (the
`Crypto.Assumptions` axioms, discharged upstream); byte-exact BLAKE2s
parity (we run SHA-256); full message serialization / MAC1 transcript;
DERP end-to-end encryption; the DISCO NaCl box and TxID unguessability.
