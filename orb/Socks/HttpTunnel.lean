import Socks.Basic
import Socks.Relay

/-!
# The HTTP CONNECT tunnel client (RFC 9110 §9.3.6)

The second egress mechanism for proxy chaining: the local node sends
`CONNECT host:port HTTP/1.1` (plus headers, terminated by a blank line) to an
upstream HTTP proxy and waits for the status-line reply. A `2xx` status opens
the tunnel; any other status (or a malformed reply) tears it down.

```
  awaitReply ──2xx, full head──────▶ cEstablished  (tunnelUp)  [terminal]
  awaitReply ──non-2xx, full head──▶ cFailed       (closeErr)  [terminal]
  awaitReply ──malformed head──────▶ cFailed       (closeErr)  [terminal]
  awaitReply ──partial (no CRLFCRLF)▶ (unchanged)  (wait)
```

`parseConnectReply` decodes the response head: it is `incomplete` until the
end-of-head marker `CRLF CRLF` is present, then `complete code` if the status
line is well-formed (`HTTP/1.x SSS`) or `error` if not. The theorems mirror the
SOCKS handshake:

* **Totality / determinism / no stuck state** (`cstep_total`,
  `cstep_deterministic`, `cstep_malformed`).
* **Established only via a 2xx status** (`enter_cEstablished_via_2xx`) and
  **non-2xx terminates** (`c_failure_terminates`, `cFailed_absorbing`,
  `cEstablished_absorbing`).
* **No-early-egress / byte-transparency** (`cstep_no_early_egress`,
  `cstep_established_transparent`), via `Socks.Relay`.
-/

namespace Socks

/-! ## Response-head parsing -/

/-- The ASCII bytes of `"HTTP/1."` — the required status-line prefix. -/
def httpPrefix : Bytes := [72, 84, 84, 80, 47, 49, 46]

/-- Is `b` an ASCII digit (`'0'`–`'9'`)? -/
def isDigit (b : UInt8) : Bool := decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)

/-- ASCII digit value (only meaningful when `isDigit b`). -/
def digitVal (b : UInt8) : Nat := b.toNat - 48

/-- Is `code` a 2xx (tunnel-success) HTTP status? -/
def statusOk (code : Nat) : Bool := decide (200 ≤ code ∧ code < 300)

/-- Locate the end of the response head: the index just past the first
`CRLF CRLF`, or `none` if the head is not yet complete. Fuel-bounded by the
buffer length, so it is a total structural recursion. -/
def findHeadEndAux : Nat → Bytes → Option Nat
  | 0, _ => none
  | fuel + 1, buf =>
    match buf with
    | 13 :: 10 :: 13 :: 10 :: _ => some 4
    | _ :: rest => (findHeadEndAux fuel rest).map (· + 1)
    | [] => none

/-- End-of-head index (just past the terminating blank line), or `none`. -/
def findHeadEnd (buf : Bytes) : Option Nat := findHeadEndAux buf.length buf

/-- Parse the HTTP CONNECT response head. `incomplete` until the head is fully
present (`findHeadEnd` succeeds); then `complete code k` for a well-formed
status line, or `error` for a malformed one. -/
def parseConnectReply (buf : Bytes) : Res Nat :=
  match findHeadEnd buf with
  | none => .incomplete
  | some k =>
    if httpPrefix.isPrefixOf buf && decide (12 ≤ buf.length)
        && isDigit (buf.getD 9 0) && isDigit (buf.getD 10 0) && isDigit (buf.getD 11 0) then
      .complete
        (digitVal (buf.getD 9 0) * 100 + digitVal (buf.getD 10 0) * 10 + digitVal (buf.getD 11 0))
        k
    else .error

/-! ## The step function -/

/-- HTTP CONNECT client phase: awaiting the reply, then a terminal. -/
inductive CPhase where
  | awaitReply
  | cEstablished
  | cFailed
deriving DecidableEq, Repr

/-- One HTTP CONNECT step. Consumes the accumulated response bytes; a partial
head stutters with `wait`, a malformed or non-2xx head fails, a 2xx head opens
the tunnel. -/
def cstep (p : CPhase) (buf : Bytes) : CPhase × Out :=
  match p with
  | .awaitReply =>
    match parseConnectReply buf with
    | .incomplete => (.awaitReply, .wait)
    | .error => (.cFailed, .closeErr)
    | .complete code _ =>
      if statusOk code then (.cEstablished, .tunnelUp)
      else (.cFailed, .closeErr)
  | .cEstablished => (.cEstablished, .wait)
  | .cFailed => (.cFailed, .wait)

/-! ## Totality and determinism -/

/-- **Totality.** Every phase/input pair has a defined transition. -/
theorem cstep_total (p : CPhase) (buf : Bytes) :
    ∃ p' o, cstep p buf = (p', o) := ⟨_, _, rfl⟩

/-- **Determinism.** The step is a function: equal inputs, equal outputs. -/
theorem cstep_deterministic {p₁ p₂ : CPhase} {b₁ b₂ : Bytes}
    (hp : p₁ = p₂) (hb : b₁ = b₂) : cstep p₁ b₁ = cstep p₂ b₂ := by
  rw [hp, hb]

/-- **A malformed response head is a total error, not a stuck state.** In
`awaitReply`, if the head is present but fails to parse, the step
deterministically terminates in `cFailed` with `closeErr`. -/
theorem cstep_malformed (buf : Bytes) (herr : parseConnectReply buf = .error) :
    cstep .awaitReply buf = (.cFailed, Out.closeErr) := by
  simp only [cstep, herr]

/-! ## Established only via 2xx; failure terminates -/

/-- `cFailed` is absorbing. -/
theorem cFailed_absorbing (buf : Bytes) :
    cstep .cFailed buf = (.cFailed, Out.wait) := rfl

/-- `cEstablished` is absorbing. -/
theorem cEstablished_absorbing (buf : Bytes) :
    cstep .cEstablished buf = (.cEstablished, Out.wait) := rfl

/-- **The tunnel is established only via a 2xx status.** Entering `cEstablished`
from a non-established phase requires `awaitReply` and a fully-parsed `2xx`
status code. -/
theorem enter_cEstablished_via_2xx {p : CPhase} {buf : Bytes}
    (hpre : p ≠ .cEstablished)
    (hpost : (cstep p buf).1 = .cEstablished) :
    p = .awaitReply ∧ ∃ code c, parseConnectReply buf = .complete code c
      ∧ statusOk code = true := by
  cases p with
  | cEstablished => exact absurd rfl hpre
  | cFailed => simp only [cstep] at hpost; exact absurd hpost (by simp)
  | awaitReply =>
    refine ⟨rfl, ?_⟩
    simp only [cstep] at hpost
    cases hp : parseConnectReply buf with
    | incomplete => rw [hp] at hpost; exact absurd hpost (by simp)
    | error => rw [hp] at hpost; exact absurd hpost (by simp)
    | complete code c =>
      rw [hp] at hpost
      by_cases hok : statusOk code = true
      · exact ⟨code, c, rfl, hok⟩
      · simp only [if_neg hok] at hpost; exact absurd hpost (by simp)

/-- **A non-2xx status terminates the tunnel — no relay.** In `awaitReply`, a
fully-parsed reply whose status is not 2xx steps to `cFailed` with `closeErr`. -/
theorem c_failure_terminates {buf : Bytes} {code c : Nat}
    (hrep : parseConnectReply buf = .complete code c) (hfail : statusOk code = false) :
    cstep .awaitReply buf = (.cFailed, Out.closeErr) := by
  simp [cstep, hrep, hfail]

/-! ## No-early-egress and byte-transparency -/

/-- The relay gate: open exactly in `cEstablished`. -/
def CPhase.up : CPhase → Bool
  | .cEstablished => true
  | _ => false

/-- Application-byte egress for the CONNECT tunnel, gated by `CPhase.up`. -/
def cEgress (p : CPhase) (dir : Dir) (app : Bytes) : Bytes :=
  relay p.up dir app

/-- **No-early-egress.** Before the tunnel is established, the relay forwards no
application bytes, in either direction. -/
theorem cstep_no_early_egress (p : CPhase) (dir : Dir) (app : Bytes)
    (h : p ≠ .cEstablished) : cEgress p dir app = [] := by
  have : p.up = false := by cases p <;> simp_all [CPhase.up]
  simp only [cEgress, this, relay_gated]

/-- **Byte-transparency once established.** After the tunnel is up, the relay is
the identity on the payload, in either direction. -/
theorem cstep_established_transparent (dir : Dir) (app : Bytes) :
    cEgress .cEstablished dir app = app := by
  simp only [cEgress, CPhase.up, relay_transparent]

end Socks
