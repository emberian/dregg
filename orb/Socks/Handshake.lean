import Socks.Addr
import Socks.Relay

/-!
# The SOCKS5 client handshake FSM (RFC 1928 / RFC 1929)

The local node, acting as a SOCKS5 *client* toward an upstream proxy, drives
this handshake to open an egress tunnel to a final target:

```
  awaitGreeting ──method 0x00──────────────▶ awaitReply     (send CONNECT)
  awaitGreeting ──method 0x02, have creds──▶ awaitAuth       (send auth)
  awaitGreeting ──method 0x02, no creds────▶ failed          (close)
  awaitGreeting ──method 0xFF / other──────▶ failed          (close)
  awaitAuth     ──status ok────────────────▶ awaitReply      (send CONNECT)
  awaitAuth     ──status fail──────────────▶ failed          (close)
  awaitReply    ──reply 0x00───────────────▶ established     (tunnelUp)   [terminal]
  awaitReply    ──reply ≠ 0x00─────────────▶ failed          (close)      [terminal]
  <any awaiting> ──malformed bytes─────────▶ failed          (close)      [terminal]
  <any awaiting> ──short buffer────────────▶ (unchanged)      (wait)
```

`hstep` is a total deterministic step function: it consumes the current
server-response buffer for the phase and returns the next state plus an egress
action. The theorems establish:

* **Totality + determinism** (`hstep_total`, `hstep_deterministic`) and, as the
  operative content, **no stuck state** (`hstep_wait_unchanged`,
  `hstep_reply_malformed`): a malformed reply is a total `error` that terminates
  in `failed`, never an undefined transition.
* **Established only via a success reply** (`enter_established_via_success`) and
  **failure terminates** (`reply_failure_terminates`, `failed_absorbing`,
  `established_absorbing`).
* **No-early-egress** (`hstep_no_early_egress`) and **byte-transparency once
  established** (`hstep_established_transparent`), via `Socks.Relay`.
-/

namespace Socks

/-- Handshake phase. The two terminals are `established` (tunnel open) and
`failed` (torn down); the three `await*` phases are reactive. -/
inductive Phase where
  | awaitGreeting
  | awaitAuth
  | awaitReply
  | established
  | failed
deriving DecidableEq, Repr

/-- Is this a reactive (awaiting-server-bytes) phase? -/
def Phase.awaiting : Phase → Bool
  | .awaitGreeting => true
  | .awaitAuth => true
  | .awaitReply => true
  | _ => false

/-- Client handshake state: the phase plus whether username/password
credentials are configured (which decides how a method-0x02 selection is
handled). -/
structure HState where
  phase : Phase
  hasAuth : Bool
deriving DecidableEq, Repr

/-- The fresh client state: the greeting has been sent, awaiting the server's
method selection. -/
def HState.init (hasAuth : Bool) : HState := ⟨.awaitGreeting, hasAuth⟩

/-! ## The per-phase server-message parsers -/

/-- SOCKS5 greeting response (RFC 1928 §3): `VER(5) METHOD(1)`. Returns the
selected method byte. A wrong version is a total error. -/
def parseMethod (buf : Bytes) : Res UInt8 :=
  match buf with
  | v :: m :: _ => if v = 0x05 then .complete m 2 else .error
  | _ => .incomplete

/-- SOCKS5 auth sub-negotiation response (RFC 1929 §2): `VER(1) STATUS(1)`.
Success iff `STATUS = 0`. The VER byte is not enforced (matching real servers
that echo either 0x01 or 0x05). -/
def parseAuthStatus (buf : Bytes) : Res Bool :=
  match buf with
  | _ :: st :: _ => .complete (st == 0x00) 2
  | _ => .incomplete

/-- SOCKS5 CONNECT reply (RFC 1928 §6): `VER(5) REP(1) RSV(1) ATYP+ADDR+PORT`.
Returns the reply code `REP`. The bind address is parsed (and discarded) via
`parseAddr`, so a malformed address is a total error. -/
def parseReply (buf : Bytes) : Res UInt8 :=
  match buf with
  | v :: rep :: _rsv :: rest =>
    if v = 0x05 then
      match parseAddr rest with
      | .complete _ c => .complete rep (3 + c)
      | .incomplete => .incomplete
      | .error => .error
    else .error
  | _ => .incomplete

/-! ## The step function -/

/-- One handshake step. Consumes the server-response buffer for the current
phase; returns the next state and the egress action. Terminal phases and short
buffers stutter with `wait`. -/
def hstep (s : HState) (buf : Bytes) : HState × Out :=
  match s.phase with
  | .awaitGreeting =>
    match parseMethod buf with
    | .incomplete => (s, .wait)
    | .error => ({s with phase := .failed}, .closeErr)
    | .complete m _ =>
      if m = 0x00 then ({s with phase := .awaitReply}, .sendConnect)
      else if m = 0x02 then
        if s.hasAuth then ({s with phase := .awaitAuth}, .sendAuth)
        else ({s with phase := .failed}, .closeErr)
      else ({s with phase := .failed}, .closeErr)
  | .awaitAuth =>
    match parseAuthStatus buf with
    | .incomplete => (s, .wait)
    | .error => ({s with phase := .failed}, .closeErr)
    | .complete ok _ =>
      if ok then ({s with phase := .awaitReply}, .sendConnect)
      else ({s with phase := .failed}, .closeErr)
  | .awaitReply =>
    match parseReply buf with
    | .incomplete => (s, .wait)
    | .error => ({s with phase := .failed}, .closeErr)
    | .complete code _ =>
      if code = 0x00 then ({s with phase := .established}, .tunnelUp)
      else ({s with phase := .failed}, .closeErr)
  | .established => (s, .wait)
  | .failed => (s, .wait)

/-! ## Totality and determinism (Theorem 1) -/

/-- **Totality.** Every state/input pair has a defined transition (the step is
a total function). -/
theorem hstep_total (s : HState) (buf : Bytes) :
    ∃ s' o, hstep s buf = (s', o) := ⟨_, _, rfl⟩

/-- **Determinism.** Equal inputs produce equal outputs — the step is a
function, so the transition relation is single-valued. -/
theorem hstep_deterministic {s₁ s₂ : HState} {b₁ b₂ : Bytes}
    (hs : s₁ = s₂) (hb : b₁ = b₂) : hstep s₁ b₁ = hstep s₂ b₂ := by
  rw [hs, hb]

/-- **No stuck state (quiescence characterization).** In a reactive phase, the
state is left unchanged *only* when the step emits `wait` (i.e. the buffer was
incomplete). Every other outcome makes progress to a new phase — there is no
silent self-loop that does work. -/
theorem hstep_wait_unchanged (s : HState) (buf : Bytes)
    (haw : s.phase.awaiting = true) (h : (hstep s buf).1 = s) :
    (hstep s buf).2 = Out.wait := by
  obtain ⟨ph, ha⟩ := s
  cases ph with
  | established => simp [Phase.awaiting] at haw
  | failed => simp [Phase.awaiting] at haw
  | awaitGreeting =>
    simp only [hstep] at h ⊢
    cases hp : parseMethod buf with
    | incomplete => rfl
    | error => rw [hp] at h; exact absurd h (by simp)
    | complete m c =>
      rw [hp] at h
      by_cases hm0 : m = 0x00
      · simp only [if_pos hm0] at h; exact absurd h (by simp)
      · by_cases hm2 : m = 0x02
        · by_cases hca : ha = true
          · simp only [if_neg hm0, if_pos hm2, if_pos hca] at h
            exact absurd h (by simp)
          · simp only [if_neg hm0, if_pos hm2, if_neg hca] at h
            exact absurd h (by simp)
        · simp only [if_neg hm0, if_neg hm2] at h; exact absurd h (by simp)
  | awaitAuth =>
    simp only [hstep] at h ⊢
    cases hp : parseAuthStatus buf with
    | incomplete => rfl
    | error => rw [hp] at h; exact absurd h (by simp)
    | complete ok c =>
      rw [hp] at h
      by_cases hok : ok = true
      · simp only [if_pos hok] at h; exact absurd h (by simp)
      · simp only [if_neg hok] at h; exact absurd h (by simp)
  | awaitReply =>
    simp only [hstep] at h ⊢
    cases hp : parseReply buf with
    | incomplete => rfl
    | error => rw [hp] at h; exact absurd h (by simp)
    | complete code c =>
      rw [hp] at h
      by_cases hc0 : code = 0x00
      · simp only [if_pos hc0] at h; exact absurd h (by simp)
      · simp only [if_neg hc0] at h; exact absurd h (by simp)

/-- **A malformed CONNECT reply is a total error, not a stuck state.** In
`awaitReply`, if the reply bytes fail to parse, the step deterministically
terminates in `failed` with a `closeErr` — a defined transition to a terminal
phase. -/
theorem hstep_reply_malformed {s : HState} (buf : Bytes)
    (hph : s.phase = .awaitReply) (herr : parseReply buf = .error) :
    hstep s buf = ({s with phase := .failed}, Out.closeErr) := by
  obtain ⟨ph, ha⟩ := s
  simp only at hph; subst hph
  simp only [hstep, herr]

/-! ## Established only via success; failure terminates (Theorem 4) -/

/-- `failed` is absorbing: a torn-down handshake never revives. -/
theorem failed_absorbing {s : HState} (h : s.phase = .failed) (buf : Bytes) :
    hstep s buf = (s, Out.wait) := by
  obtain ⟨ph, ha⟩ := s
  simp only at h; subst h; simp only [hstep]

/-- `established` is absorbing: an open tunnel is never re-handshaked. -/
theorem established_absorbing {s : HState} (h : s.phase = .established)
    (buf : Bytes) : hstep s buf = (s, Out.wait) := by
  obtain ⟨ph, ha⟩ := s
  simp only at h; subst h; simp only [hstep]

/-- **Established is reached only via a success reply.** If a step lands in
`established` from a non-established state, the prior phase was `awaitReply` and
the reply parsed to the success code `0x00`. There is no other door into the
tunnel. -/
theorem enter_established_via_success {s : HState} {buf : Bytes}
    (hpre : s.phase ≠ .established)
    (hpost : (hstep s buf).1.phase = .established) :
    s.phase = .awaitReply ∧ ∃ c, parseReply buf = .complete 0x00 c := by
  obtain ⟨ph, ha⟩ := s
  cases ph with
  | established => exact absurd rfl hpre
  | failed => simp only [hstep] at hpost; exact absurd hpost (by simp)
  | awaitGreeting =>
    simp only [hstep] at hpost
    cases hp : parseMethod buf with
    | incomplete => rw [hp] at hpost; exact absurd hpost (by simp)
    | error => rw [hp] at hpost; exact absurd hpost (by simp)
    | complete m c =>
      rw [hp] at hpost
      by_cases hm0 : m = 0x00
      · simp only [if_pos hm0] at hpost; exact absurd hpost (by simp)
      · by_cases hm2 : m = 0x02
        · by_cases hca : ha = true <;>
            simp_all only [if_pos, if_neg] <;> exact absurd hpost (by simp)
        · simp only [if_neg hm0, if_neg hm2] at hpost; exact absurd hpost (by simp)
  | awaitAuth =>
    simp only [hstep] at hpost
    cases hp : parseAuthStatus buf with
    | incomplete => rw [hp] at hpost; exact absurd hpost (by simp)
    | error => rw [hp] at hpost; exact absurd hpost (by simp)
    | complete ok c =>
      rw [hp] at hpost
      by_cases hok : ok = true <;>
        simp_all only [if_pos, if_neg] <;> exact absurd hpost (by simp)
  | awaitReply =>
    refine ⟨rfl, ?_⟩
    simp only [hstep] at hpost
    cases hp : parseReply buf with
    | incomplete => rw [hp] at hpost; exact absurd hpost (by simp)
    | error => rw [hp] at hpost; exact absurd hpost (by simp)
    | complete code c =>
      rw [hp] at hpost
      by_cases hc0 : code = 0x00
      · subst hc0; exact ⟨c, rfl⟩
      · simp only [if_neg hc0] at hpost; exact absurd hpost (by simp)

/-- **A failure reply code terminates the handshake — no tunnel.** In
`awaitReply`, a fully-parsed reply whose code is not `0x00` steps to `failed`
with `closeErr`, never to `established`. -/
theorem reply_failure_terminates {s : HState} {buf : Bytes} {c : Nat}
    (hph : s.phase = .awaitReply) {rep : UInt8}
    (hrep : parseReply buf = .complete rep c) (hfail : rep ≠ 0x00) :
    (hstep s buf).1.phase = .failed ∧ (hstep s buf).2 = Out.closeErr := by
  obtain ⟨ph, ha⟩ := s
  simp only at hph; subst hph
  refine ⟨?_, ?_⟩ <;> simp [hstep, hrep, if_neg hfail]

/-! ## No-early-egress and byte-transparency (Theorems 3 and 5) -/

/-- The relay gate: open exactly in `established`. -/
def HState.up (s : HState) : Bool :=
  match s.phase with
  | .established => true
  | _ => false

/-- Application-byte egress for the handshake: gated by `HState.up`, delegating
to `Socks.relay`. -/
def hEgress (s : HState) (dir : Dir) (app : Bytes) : Bytes :=
  relay s.up dir app

/-- `up` is false in every non-established phase. -/
theorem HState.up_false {s : HState} (h : s.phase ≠ .established) :
    s.up = false := by
  unfold HState.up
  cases hph : s.phase <;> simp_all

/-- **No-early-egress.** Before the tunnel is established, the relay forwards no
application bytes, in either direction. The gate stays closed until — by
`enter_established_via_success` — a success reply opens it. -/
theorem hstep_no_early_egress (s : HState) (dir : Dir) (app : Bytes)
    (h : s.phase ≠ .established) : hEgress s dir app = [] := by
  simp only [hEgress, HState.up_false h, relay_gated]

/-- **Byte-transparency once established.** After the tunnel is up, the relay is
the identity on the payload, in either direction: no application byte is
altered. -/
theorem hstep_established_transparent (s : HState) (dir : Dir) (app : Bytes)
    (h : s.phase = .established) : hEgress s dir app = app := by
  have : s.up = true := by unfold HState.up; rw [h]
  simp only [hEgress, this, relay_transparent]

end Socks
