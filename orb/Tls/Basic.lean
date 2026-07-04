/-!
# TLS record/handshake state machine with kernel offload — core types

A sans-IO model of the per-connection TLS lifecycle for a server front
end: ciphertext accumulation, the handshake (including early — 0.5-RTT —
application data drained *during* the handshake), the established
userspace record path, the kernel record-layer offload window (TLS ULP
attach, then TX-key then RX-key install, with the half-configured
teardown edge in between), the fully offloaded plaintext path, and
closure.

The machine is a total, deterministic function

    step : Config → St → Input → St × Eff

All cryptography (AEAD record protection, KDF-derived key material, the
handshake transcript) enters as named function-valued fields of
`Config`: the machine treats them as uninterpreted total functions, so
every theorem holds uniformly over every crypto behavior. This is the
named crypto-axiom boundary — the theorems here are about the state
machine, not about the cipher.

Two lifecycle subtleties are modeled explicitly because the security
theorems are vacuous without them:

* **Consume-and-vanish.** Offloading the record layer to the kernel
  extracts the traffic secrets out of the userspace connection and
  destroys it; after the handoff the TLS session identity lives only in
  the kernel socket. The step reports, as ghost data, which userspace
  record connections it *used* (applied a record-layer effect to) and
  which it *consumed* (extracted the secrets of). The linearity
  theorems say a connection is consumed at most once and never used
  after consumption.

* **The half-configured window.** The TX-direction and RX-direction key
  installs are separate kernel operations. Between them the socket is
  half-configured, and userspace secrets are already gone — a failure
  there cannot fall back to the userspace path and must tear the
  connection down immediately, without emitting any parked plaintext.
-/

namespace Tls

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-- Opaque handle to a userspace TLS *handshake* engine instance. -/
structure HsConn where
  id : Nat
deriving Repr, DecidableEq

/-- Opaque handle to a userspace TLS *record* engine: an established
connection holding the traffic secrets and performing AEAD record
protection in this machine's process. -/
structure RecConn where
  id : Nat
deriving Repr, DecidableEq

/-- Opaque symmetric key material for one direction (cipher key + IV +
record sequence number), in the form the kernel install takes. -/
structure KeyMat where
  id : Nat
deriving Repr, DecidableEq

/-- Both directions of extracted traffic secrets. -/
structure Secrets where
  tx : KeyMat
  rx : KeyMat
deriving Repr, DecidableEq

/-- Application protocol negotiated by ALPN (inert data here; the
application-protocol machines live elsewhere). -/
inductive Alpn where
  | h1
  | h2
deriving Repr, DecidableEq

/-- Outcome of feeding accumulated ciphertext to the handshake engine. -/
inductive HsOut where
  /-- Not even one complete record is available: keep accumulating. -/
  | insufficient
  /-- Handshake progressed: successor engine, ciphertext consumed, a
  flight to send, and any early (0.5-RTT) application plaintext drained
  while the handshake is still in progress. -/
  | more (hs : HsConn) (consumed : Nat) (send : Bytes) (early : Bytes)
  /-- Handshake complete: the established record engine, ciphertext
  consumed, the final flight, the negotiated ALPN, and early plaintext
  drained together with the peer's finish. -/
  | done (rc : RecConn) (consumed : Nat) (send : Bytes) (alpn : Alpn)
         (early : Bytes)
  /-- Handshake failure (malformed record, bad MAC, policy refusal). -/
  | fail

/-- Outcome of feeding accumulated ciphertext to the established record
engine (the AEAD-open path). -/
inductive RecOut where
  /-- Records decrypted (possibly zero): successor engine, ciphertext
  consumed, plaintext produced. -/
  | more (rc : RecConn) (consumed : Nat) (plain : Bytes)
  /-- The peer's close_notify, preceded by `plain` (data arriving ahead
  of the close is still valid). -/
  | closeNotify (consumed : Nat) (plain : Bytes)
  /-- Record-layer failure (bad MAC, malformed record). -/
  | fail

/-- The per-connection lifecycle phase. -/
inductive Phase where
  /-- Accumulating ciphertext toward the first complete handshake
  record. -/
  | accum (hs : HsConn) (buf : Bytes)
  /-- Handshake in progress; early (0.5-RTT) plaintext may drain here. -/
  | handshaking (hs : HsConn) (buf : Bytes)
  /-- Established, userspace record path. `buf` accumulates undecoded
  ciphertext (partial records survive across receives). -/
  | estabUser (alpn : Alpn) (rc : RecConn) (buf : Bytes)
  /-- Kernel offload requested: the ULP attach was emitted and the
  verdict is pending. The userspace connection is still whole — if the
  kernel lacks the facility, the machine falls back to `estabUser`.
  `buf` is leftover ciphertext, `pend` parked application plaintext. -/
  | offloadAttach (alpn : Alpn) (rc : RecConn) (buf : Bytes) (pend : Bytes)
  /-- TX-key install in flight. The userspace connection has been
  **consumed**: its secrets now exist only as the not-yet-installed RX
  key material carried here. `pend` is parked application plaintext,
  flushed only on full configuration. -/
  | installingTx (alpn : Alpn) (rx : KeyMat) (pend : Bytes)
  /-- RX-key install in flight: TX installed, RX pending — the
  **half-configured socket**. No fallback exists from here; the only
  exit besides completion is immediate teardown. -/
  | installingRx (alpn : Alpn) (pend : Bytes)
  /-- Fully offloaded: the kernel owns the record layer. This machine
  reads and writes plaintext on the socket; no userspace TLS state
  exists any more. -/
  | estabOffload (alpn : Alpn)
  /-- close_notify sent; draining the send path. No plaintext may be
  produced from here on. -/
  | closing
  /-- Terminal. -/
  | closed
deriving Repr, DecidableEq

/-- Inputs: everything the environment can tell the machine. -/
inductive Input where
  /-- Bytes from the socket: ciphertext before offload, plaintext
  (already decrypted by the kernel) once offloaded. -/
  | bytesReceived (data : Bytes)
  /-- The application asks to send plaintext. -/
  | appData (data : Bytes)
  /-- Kernel: the TLS ULP attached; offload can proceed. -/
  | ulpAttached
  /-- Kernel: no kernel TLS on this socket; fall back to userspace. -/
  | ulpUnavailable
  /-- Kernel: the pending key-install step (TX or RX) succeeded. -/
  | installOk
  /-- Kernel: the pending offload step failed. Once secrets extraction
  has happened this leaves a half-configured socket, and the only safe
  move is teardown. -/
  | installFailed
  /-- Local close requested (shutdown, admin). -/
  | closeRequested
  /-- The peer closed (EOF on receive). -/
  | peerClosed
  /-- The outbound queue drained (finishes `closing`). -/
  | sendDrained
deriving Repr, DecidableEq

/-- Outputs: everything the machine can ask the environment to do. -/
inductive Output where
  /-- Record-layer bytes (handshake flight / ciphertext / alert) to the
  wire. Never application plaintext. -/
  | send (data : Bytes)
  /-- Plaintext write on the offloaded socket (the kernel seals it).
  Only legal on a fully configured socket. -/
  | sendPlain (data : Bytes)
  /-- Decrypted application data, to the application. -/
  | deliverPlain (data : Bytes)
  /-- Early (0.5-RTT) application data, to the application. A separate
  constructor so the early-data acceptance theorem is visible in the
  output trace. -/
  | deliverEarly (data : Bytes)
  /-- Ask the kernel to attach the TLS ULP to the socket. -/
  | attachUlp
  /-- Install transmit-direction key material in the kernel. -/
  | installTx (k : KeyMat)
  /-- Install receive-direction key material in the kernel. -/
  | installRx (k : KeyMat)
  /-- Close the socket. Terminal. -/
  | close
deriving Repr, DecidableEq

/-- `true` exactly on outputs that carry application plaintext. -/
def Output.carriesPlain : Output → Bool
  | .sendPlain _ => true
  | .deliverPlain _ => true
  | .deliverEarly _ => true
  | _ => false

/-- Static configuration and the named crypto-effect vocabulary. Every
function-valued field is an uninterpreted total function — the crypto
axiom boundary: theorems about `step` hold for all of them. -/
structure Config where
  /-- Fresh handshake engine for a new connection. -/
  hsInit : HsConn
  /-- Offload policy: attempt the kernel record layer after the
  handshake completes. -/
  ktls : Bool
  /-- Explicit early-data acceptance flag. Early (0.5-RTT) plaintext is
  delivered iff this is set; replay-bounding an accepted early-data
  unit is the transport lane's obligation, keyed on this same flag. -/
  earlyDataAccepted : Bool
  /-- Encoded fatal alert record (sent before failure teardown). -/
  fatalAlert : Bytes
  /-- Feed ciphertext to the handshake engine (KDF and transcript live
  behind this boundary). -/
  hsFeed : HsConn → Bytes → HsOut
  /-- AEAD-open: feed ciphertext to the established record engine. -/
  recOpen : RecConn → Bytes → RecOut
  /-- AEAD-seal: protect plaintext for the wire. -/
  recSeal : RecConn → Bytes → RecConn × Bytes
  /-- The encrypted close_notify record for this connection. -/
  recCloseNotify : RecConn → Bytes
  /-- Extract both directions of traffic secrets for kernel install.
  This is the **consuming** operation: the caller must destroy the
  connection and never touch it again. -/
  extractSecrets : RecConn → Secrets

/-- Machine state: the lifecycle phase plus the ghost consumed-set. -/
structure St where
  phase : Phase
  /-- Ghost: record connections whose secrets have been extracted. -/
  consumed : List RecConn
deriving Repr

/-- The observable and ghost effect of one step. -/
structure Eff where
  out : List Output := []
  /-- Ghost: record connections a record-layer effect was applied to
  in this step. -/
  uses : List RecConn := []
  /-- Ghost: record connections consumed (secrets extracted) in this
  step. -/
  consumes : List RecConn := []
deriving Repr, DecidableEq

/-- Initial state: accumulating ciphertext toward the first handshake
record; nothing consumed. -/
def init (cfg : Config) : St :=
  { phase := .accum cfg.hsInit [], consumed := [] }

end Tls
