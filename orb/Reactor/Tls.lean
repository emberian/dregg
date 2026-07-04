import Proto.Basic
import Proto.Step
import Tls.Basic
import Tls.Step
import Tls.Theorems
import Reactor.Config

/-!
# Reactor.Tls — wiring the real TLS engine into the connection FSM

The connection FSM (`Proto`) takes its TLS record/handshake behaviour as three
abstract `Config` fields:

* `hsFeed  : TlsConn → Bytes → HsOut`                     (drive the handshake)
* `tlsRecv : TlsConn → Bytes → Option (TlsConn × Nat × Bytes)`  (AEAD-open)
* `tlsSend : TlsConn → Bytes → TlsConn × Bytes`           (AEAD-seal)

`Reactor.Config.demoConfig` stubs all three to inert/refusing totals
(`hsFeed := fun _ _ => .fail`, `tlsRecv := fun _ _ => none`, …), so every FSM
theorem held "for all TLS codecs" but no *real* record layer was ever plugged
in — the same island the arena parser and body reader were pulled off of.

The proto-codec seed reshaped `Proto.TlsConn` from a `{id : Nat}` stub to carry
the real lifecycle record `st : Tls.St` (see `PROTO-CODEC-SEED-README.md`), so
the live TLS state now rides through the FSM's opaque handle. This file drives
the *real* `Tls` state machine (`Tls.step`, `Tls.Basic`, `Tls.Step`,
`Tls.Theorems`) through that handle:

* `hsFeedReal` / `tlsRecvReal` / `tlsSendReal` — adapters that feed the FSM's
  ciphertext/plaintext into `Tls.step` and read the successor `Tls.St` and the
  emitted `Tls.Output`s back out into the FSM's `HsOut` / decrypted-plaintext /
  wire-bytes vocabulary. Each adapter reports `consumed = buf.length`: the
  `Tls` machine owns the partial-record buffering internally (inside its
  `Phase`), so the FSM's external ciphertext accumulation stays empty and there
  is no double-buffering.
* `wireTls : Tls.Config → Proto.Config → Proto.Config` — the transformer that
  installs those three adapters, leaving every other field of the base config
  untouched. `demoConfig` is *not* edited; `wiredDemoConfig` is the concrete
  reactor config with the real TLS engine plugged in.

## The seam theorem

`tls_no_plaintext_seam` ties `Tls.no_plain_after_close` to the FSM wiring: once
the TLS record layer underlying a `TlsConn` is torn down (its `Tls.Phase` is
`closing` or `closed`), **no** sequence of inputs the FSM can drive through the
adapters ever surfaces application plaintext — `plainBytes` of every step's
output is `[]`. Supporting this:

* `tlsRecv_plain_nil_after_close` — the decrypted plaintext the record codec
  hands *back into the FSM* on a receive is empty once torn down (so an FSM
  `runH1`/`wsBytes`/relay sees no new plaintext), and
* `tlsTunnel_no_forward_after_close` — an FSM `onBytes` step on a TLS CONNECT
  tunnel whose record layer is gone either closes or forwards **nothing**
  upstream: the composed wiring emits no plaintext-carrying forward.
* `tlsSend_absorbing` / `tlsRecv_absorbing` — the adapters preserve teardown,
  so the FSM can never revive a torn-down record layer.

All three record adapters drive the same `Tls.step`, so a run of FSM receives
corresponds to a `Tls.run` over the induced input trace, and the trace-form
security theorem of the TLS machine transfers verbatim.
-/

namespace Reactor
namespace TlsWire

open Proto (Bytes TlsConn Config HsOut)

/-! ## Reading `Tls.Output` lists back into FSM byte vocabulary -/

/-- Wire (record-layer) bytes carried by one output, if any. `.send` is the
only wire-carrying constructor; it never carries application plaintext. -/
def sendOf : Tls.Output → Option Bytes
  | .send b => some b
  | _ => none

/-- Decrypted application plaintext carried by one output, if any. Exactly the
`.deliverPlain` constructor. -/
def plainOf : Tls.Output → Option Bytes
  | .deliverPlain b => some b
  | _ => none

/-- Early (0.5-RTT) plaintext carried by one output, if any. -/
def earlyOf : Tls.Output → Option Bytes
  | .deliverEarly b => some b
  | _ => none

/-- Concatenated wire bytes of a step's outputs (handshake flights, sealed
records, alerts). -/
def sendBytes (out : List Tls.Output) : Bytes := (out.filterMap sendOf).flatten

/-- Concatenated decrypted application plaintext of a step's outputs. -/
def plainBytes (out : List Tls.Output) : Bytes := (out.filterMap plainOf).flatten

/-- Concatenated early (0.5-RTT) plaintext of a step's outputs. -/
def earlyBytes (out : List Tls.Output) : Bytes := (out.filterMap earlyOf).flatten

/-- ALPN carried by the TLS handshake back into the FSM's ALPN vocabulary. -/
def alpnToProto : Tls.Alpn → Proto.Alpn
  | .h1 => .h1
  | .h2 => .h2

/-! ## The adapters: drive the real `Tls.step` through the FSM's handle -/

/-- Feed accumulated ciphertext to the real TLS handshake engine. Drives
`Tls.step` on the carried `Tls.St` with `bytesReceived buf`, then reads the
successor phase back into `Proto.HsOut`:

* still handshaking (`accum`/`handshaking`) → `.more` with the flight to send;
* handshake complete to the userspace record path (`estabUser`) → `.done` with
  `ktls := false`;
* handshake complete into the kernel-offload window (`offloadAttach`) → `.done`
  with `ktls := true`;
* torn down (`closed`, e.g. an alert/failure) → `.fail`.

`consumed := buf.length` — the `Tls` machine buffered any partial record
internally, so the FSM keeps no leftover ciphertext. -/
def hsFeedReal (tcfg : Tls.Config) (tc : TlsConn) (buf : Bytes) : HsOut :=
  let r := Tls.step tcfg tc.st (.bytesReceived buf)
  match r.1.phase with
  | .accum _ _ => .more ⟨r.1⟩ buf.length (sendBytes r.2.out)
  | .handshaking _ _ => .more ⟨r.1⟩ buf.length (sendBytes r.2.out)
  | .estabUser alpn _ _ =>
    .done ⟨r.1⟩ buf.length (sendBytes r.2.out) (alpnToProto alpn) false (earlyBytes r.2.out)
  | .offloadAttach alpn _ _ _ =>
    .done ⟨r.1⟩ buf.length (sendBytes r.2.out) (alpnToProto alpn) true (earlyBytes r.2.out)
  | _ => .fail

/-- Decode established-session ciphertext with the real record engine. Drives
`Tls.step` with `bytesReceived buf`; a step into the terminal `closed` phase (a
record-layer failure — bad MAC / malformed record) becomes the FSM's `none`
(which closes the connection). Otherwise returns the successor connection, the
whole buffer as consumed, and the decrypted plaintext. -/
def tlsRecvReal (tcfg : Tls.Config) (tc : TlsConn) (buf : Bytes) :
    Option (TlsConn × Nat × Bytes) :=
  let r := Tls.step tcfg tc.st (.bytesReceived buf)
  match r.1.phase with
  | .closed => none
  | _ => some (⟨r.1⟩, buf.length, plainBytes r.2.out)

/-- Encrypt (seal) plaintext for sending on an established session. Drives
`Tls.step` with `appData plain`; the sealed record surfaces as a `.send`
output, collected into the FSM's wire bytes. After teardown the machine emits
nothing, so the wire bytes are empty. -/
def tlsSendReal (tcfg : Tls.Config) (tc : TlsConn) (plain : Bytes) : TlsConn × Bytes :=
  let r := Tls.step tcfg tc.st (.appData plain)
  (⟨r.1⟩, sendBytes r.2.out)

/-- The config transformer: install the three real TLS adapters into a base
`Proto.Config`, leaving every other field untouched. `demoConfig` is not
edited. -/
def wireTls (tcfg : Tls.Config) (cfg : Config) : Config :=
  { cfg with
      hsFeed := hsFeedReal tcfg
      tlsRecv := tlsRecvReal tcfg
      tlsSend := tlsSendReal tcfg }

/-- A concrete crypto boundary: an inert-but-total `Tls.Config`. The seam
theorems quantify over *every* `Tls.Config`, so this instance is only here to
exhibit a fully-plugged reactor config; the crypto behaviour behind these
fields is irrelevant to the lifecycle security property. -/
def demoTlsCfg : Tls.Config where
  hsInit := ⟨0⟩
  ktls := false
  earlyDataAccepted := false
  fatalAlert := []
  hsFeed := fun _ _ => .fail
  recOpen := fun _ _ => .fail
  recSeal := fun rc b => (rc, b)
  recCloseNotify := fun _ => []
  extractSecrets := fun _ => ⟨⟨0⟩, ⟨0⟩⟩

/-- The concrete reactor config with the real TLS engine wired in over the
arena-backed HTTP/1.1 `demoConfig`. -/
def wiredDemoConfig : Config := wireTls demoTlsCfg Reactor.Config.demoConfig

/-! ## The wired fields are exactly the adapters (no drift) -/

theorem wireTls_hsFeed (tcfg : Tls.Config) (cfg : Config) :
    (wireTls tcfg cfg).hsFeed = hsFeedReal tcfg := rfl

theorem wireTls_tlsRecv (tcfg : Tls.Config) (cfg : Config) :
    (wireTls tcfg cfg).tlsRecv = tlsRecvReal tcfg := rfl

theorem wireTls_tlsSend (tcfg : Tls.Config) (cfg : Config) :
    (wireTls tcfg cfg).tlsSend = tlsSendReal tcfg := rfl

theorem wiredDemoConfig_tlsSend :
    wiredDemoConfig.tlsSend = tlsSendReal demoTlsCfg := rfl

/-! ## No plaintext surfaces after the record layer is torn down -/

/-- An output that carries no plaintext yields nothing under `plainOf`
(`deliverPlain`, the only `plainOf`-`some` constructor, has
`carriesPlain = true`). -/
theorem plainOf_none_of_no_plain (o : Tls.Output) (h : o.carriesPlain = false) :
    plainOf o = none := by
  cases o <;> simp_all [plainOf, Tls.Output.carriesPlain]

/-- If every output of a list is non-plaintext, filtering for plaintext yields
the empty list. -/
theorem filterMap_plainOf_nil (out : List Tls.Output)
    (h : ∀ o ∈ out, o.carriesPlain = false) : out.filterMap plainOf = [] := by
  induction out with
  | nil => rfl
  | cons o r ih =>
    have ho : plainOf o = none := plainOf_none_of_no_plain o (h o (by simp))
    have hr : r.filterMap plainOf = [] := ih (fun x hx => h x (List.mem_cons_of_mem o hx))
    simp [List.filterMap_cons, ho, hr]

/-- **The core surfacing lemma.** Once the TLS phase is closing/closed, the
decrypted plaintext any step surfaces (`plainBytes` of its outputs) is empty —
directly from `Tls.no_plain_in_close_step`. -/
theorem step_plainBytes_nil_after_close (tcfg : Tls.Config) (s : Tls.St)
    (i : Tls.Input) (h : s.phase.closingOrClosed = true) :
    plainBytes (Tls.step tcfg s i).2.out = [] := by
  unfold plainBytes
  rw [filterMap_plainOf_nil _ (Tls.no_plain_in_close_step tcfg s i h)]
  rfl

/-- `tlsRecvReal` is `none`, or exactly the canonical `some` carrying the driven
step's successor and surfaced plaintext. -/
theorem tlsRecvReal_cases (tcfg : Tls.Config) (tc : TlsConn) (buf : Bytes) :
    tlsRecvReal tcfg tc buf = none ∨
    tlsRecvReal tcfg tc buf
      = some (⟨(Tls.step tcfg tc.st (.bytesReceived buf)).1⟩, buf.length,
              plainBytes (Tls.step tcfg tc.st (.bytesReceived buf)).2.out) := by
  simp only [tlsRecvReal]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The seam, step form.** For any base config, once the record layer
underlying `tc` is torn down, the plaintext `tlsRecvReal` hands *back into the
FSM* is empty in the `some` (still-open-ish) branch — a receive on a torn-down
TLS connection surfaces no new application plaintext to `runH1`/`wsBytes`/relay
forwarding. -/
theorem tlsRecv_plain_nil_after_close (tcfg : Tls.Config) (tc : TlsConn)
    (buf : Bytes) (h : tc.st.phase.closingOrClosed = true)
    {tc' : TlsConn} {n : Nat} {plain : Bytes}
    (heq : tlsRecvReal tcfg tc buf = some (tc', n, plain)) : plain = [] := by
  rcases tlsRecvReal_cases tcfg tc buf with hn | hs
  · rw [hn] at heq; exact absurd heq (by simp)
  · rw [hs] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    rw [← heq.2.2]
    exact step_plainBytes_nil_after_close tcfg tc.st (.bytesReceived buf) h

/-- The record adapters preserve teardown: a `tlsSend` on a torn-down
connection leaves it torn down. The FSM can never revive the record layer. -/
theorem tlsSend_absorbing (tcfg : Tls.Config) (tc : TlsConn) (plain : Bytes)
    (h : tc.st.phase.closingOrClosed = true) :
    (tlsSendReal tcfg tc plain).1.st.phase.closingOrClosed = true :=
  Tls.close_absorbing tcfg tc.st (.appData plain) h

/-- Likewise `tlsRecv`: in the `some` branch the successor connection is still
torn down. -/
theorem tlsRecv_absorbing (tcfg : Tls.Config) (tc : TlsConn) (buf : Bytes)
    (h : tc.st.phase.closingOrClosed = true)
    {tc' : TlsConn} {n : Nat} {plain : Bytes}
    (heq : tlsRecvReal tcfg tc buf = some (tc', n, plain)) :
    tc'.st.phase.closingOrClosed = true := by
  rcases tlsRecvReal_cases tcfg tc buf with hn | hs
  · rw [hn] at heq; exact absurd heq (by simp)
  · rw [hs] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    rw [← heq.1]
    exact Tls.close_absorbing tcfg tc.st (.bytesReceived buf) h

/-! ## The trace seam: no plaintext ever, tying `Tls.no_plain_after_close` -/

/-- **`tls_no_plaintext_seam`.** For a `TlsConn` whose underlying TLS record
layer is torn down (`closing`/`closed`), *no* input sequence driven through the
wired adapters ever surfaces application plaintext: `plainBytes` of every step's
output along the run is `[]`. This is exactly `Tls.no_plain_after_close`
transported through the FSM's plaintext-reading vocabulary — the composition of
the FSM TLS wiring with the TLS machine's consume-and-vanish / no-plaintext-
after-close discipline.

The adapters all drive `Tls.step tcfg tc.st ·`, so a sequence of FSM receives is
a `Tls.run tcfg tc.st is`; the security property of the record machine holds for
the whole trace. -/
theorem tls_no_plaintext_seam (tcfg : Tls.Config) (tc : TlsConn)
    (h : tc.st.phase.closingOrClosed = true) (is : List Tls.Input) :
    ∀ e ∈ (Tls.run tcfg tc.st is).2, plainBytes e.out = [] := by
  intro e he
  unfold plainBytes
  rw [filterMap_plainOf_nil _ (Tls.no_plain_after_close tcfg tc.st h is e he)]
  rfl

/-! ## FSM-level corollary: a torn-down TLS tunnel forwards nothing -/

/-- **Composed at the FSM `onBytes`.** In the TLS CONNECT-tunnel state
(`tlsTunnel`), with the wired config, once the record layer underlying `tc` is
torn down, a received-bytes step either closes the connection (record-layer
failure → `none` → `closeNow`) or forwards **nothing** upstream. The wiring
emits no plaintext-carrying forward after teardown — the FSM `onBytes` composed
with `tlsRecv_plain_nil_after_close`. -/
theorem tlsTunnel_no_forward_after_close (tcfg : Tls.Config) (cfg : Config)
    (tc : TlsConn) (tlsBuf : Bytes) (fd : Nat) (data : Bytes)
    (h : tc.st.phase.closingOrClosed = true) :
    (Proto.onBytes (wireTls tcfg cfg) (.tlsTunnel tc tlsBuf fd) data).closeNow = true ∨
    (Proto.onBytes (wireTls tcfg cfg) (.tlsTunnel tc tlsBuf fd) data).outs = [] := by
  simp only [Proto.onBytes, wireTls_tlsRecv]
  cases hrec : tlsRecvReal tcfg tc (tlsBuf ++ data) with
  | none => exact Or.inl rfl
  | some v =>
    obtain ⟨tc', n, plain⟩ := v
    have hp : plain = [] := tlsRecv_plain_nil_after_close tcfg tc (tlsBuf ++ data) h hrec
    subst hp
    exact Or.inr (by simp)

end TlsWire
end Reactor
