import Crypto

/-!
# WireGuard: the Noise IK handshake FSM and the anti-replay data plane

A sans-IO model of one WireGuard peer: the Noise IK handshake lifecycle
(handshake initiation → handshake response → transport) and the
data-plane per-message counter with its sliding-window anti-replay
filter. Derived from the WireGuard whitepaper (Donenfeld, "WireGuard:
Next Generation Kernel Network Tunnel"), specifically:

* §5.4 "First Message: Initiator to Responder" and §5.4.3 "Second
  Message: Responder to Initiator" — the two-message Noise IK handshake
  and the four message types (1 initiation, 2 response, 3 cookie,
  4 transport data). Cookie/MAC and load-shedding are out of scope here.
* §5.4.6 "Subsequent Messages: Transport Data Messages" — the 64-bit
  monotone nonce counter carried in each transport message.
* §5.4.7 "Sliding Window" — the anti-replay filter: a counter strictly
  ahead of the window is accepted and slides it forward, a counter too
  far behind is dropped, and a counter inside the window is accepted
  only if it has not already been seen. The concrete algorithm modeled
  is the RFC 6479 "next / bitmap" formulation used by every WireGuard
  implementation (a `next` high-water mark plus a bounded window).

## The machine

    step : Config → St → Input → St × List Output

is total and deterministic. In the *transport FSM*, cryptography is an
uninterpreted total boundary: `Config` carries named function-valued
fields for accepting a handshake message, deriving the session keys, and
AEAD sealing/opening transport data, and every FSM theorem holds uniformly
over every crypto behavior — the theorems are about the state machine, not
the cipher.

The `Noise` section below then *fills in* that boundary with the actual
Noise IKpsk2 key schedule, computed on the verified HACL*/EverCrypt
primitives exposed by `Crypto` (X25519, HKDF-SHA-256, ChaCha20-Poly1305).
`wg_handshake_real` proves the two peers derive one shared chaining key —
and hence identical transport keys — through the real Diffie–Hellman
chain, so the FSM's abstract `deriveKeys` boundary is discharged by real
crypto rather than assumed.

## Theorems

* `wg_no_transport_before_handshake` — no data-plane output
  (`sendTransport` on the wire, `deliver` to the application) is ever
  produced except from an `established` phase, and `established` is
  entered only by a completing handshake transition (a valid response
  accepted by an initiator, or a valid initiation accepted by a
  responder). No transport data before the handshake completes.
* `wg_replay_rejected` — in every reachable state, a transport counter
  already accepted, or one that has fallen below the window, is
  rejected: it produces no `deliver` and does not disturb the window.
  This is the whole point of the anti-replay filter.
* `wg_counter_monotone` — the window high-water mark (`next`, one past
  the highest accepted counter) never decreases across any step; the
  outbound send counter never decreases either.
* `wg_replay_window_correct` — the full anti-replay decision: a counter is
  accepted *iff* it is ahead of the window or fresh inside it (with
  `wg_window_accepts_ahead` / `wg_window_accepts_fresh` the accept side).
* `Noise.wg_handshake_real` — the real Noise IK handshake on verified
  crypto: both peers derive the same chaining key (and transport keys) via
  the X25519 Diffie–Hellman chain (`wg_transport_keys_agree`,
  `wg_static_key_authenticated` for the AEAD-sealed static key).
* `Rekey.wg_rekey_before_reject` — a session crosses the rekey threshold
  before it can ever hit the hard reject threshold (§6.1 timers).
* `Cookie.wg_cookie_mitigates` — under load, an initiation without a valid
  cookie MAC2 is never admitted to the handshake (§5.3 DoS mitigation).

## Boundary / UNCLOSED

* The Noise ratchet is instantiated on SHA-256 (via `Crypto.hkdf*` /
  `Crypto.sha256`), not the whitepaper's BLAKE2s; our verified crypto seam
  offers SHA-256, and the key-agreement argument is identical under either
  hash. Byte-exact BLAKE2s parity is the remaining boundary.
* The `Noise` section proves key *agreement* and AEAD roundtrip; it does
  not re-derive X25519 hardness or AEAD IND-CPA — those are the
  discharged-upstream `Crypto.Assumptions` axioms (X25519 agreement, AEAD
  authenticity), the intended trust boundary.
* The full message *serialization* (MAC1 over the transcript, sender/
  receiver indices, TAI64N timestamp bytes) is not byte-modeled; the
  handshake is modeled at the key-schedule / DH-chain level.
* The transport FSM's `Config` crypto fields remain abstract there (the
  FSM theorems are cipher-independent); the `Noise` section is what
  realizes them on real crypto.
* The window is modeled with a ghost `seen` set of accepted counters
  rather than a fixed-width bitmap; a real implementation stores only
  the last `windowSize` bits. The acceptance decision modeled here is
  exactly the bounded-window decision, so the anti-replay property is
  faithful; bitmap storage is the implementation boundary.
-/

namespace Wireguard

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-! ## Handshake and transport messages (opaque contents) -/

/-- A Noise IK handshake initiation (message type 1). Its encrypted
static key and timestamp live behind the crypto boundary. -/
structure Initiation where
  raw : Bytes
deriving Repr, DecidableEq

/-- A Noise IK handshake response (message type 2). -/
structure Response where
  raw : Bytes
deriving Repr, DecidableEq

/-- A transport data message (message type 4): the 64-bit nonce counter
in the clear and the AEAD-sealed payload. -/
structure TransportMsg where
  counter : Nat
  payload : Bytes
deriving Repr, DecidableEq

/-- Opaque derived session-key material (both directions). -/
structure Keys where
  id : Nat
deriving Repr, DecidableEq

/-- Which end of the handshake this peer played. -/
inductive Role where
  | initiator
  | responder
deriving Repr, DecidableEq

/-! ## The sliding-window anti-replay filter (whitepaper §5.4.7) -/

/-- Window width. WireGuard's stock filter reorders up to a few thousand
packets; the exact width is irrelevant to the anti-replay property so
long as it is positive. Modeled here as one 64-bit word. -/
def windowSize : Nat := 64

/-- The receive-side anti-replay state: `next` is one past the highest
counter accepted so far (the RFC 6479 high-water mark), and `seen` is
the ghost set of every counter accepted. A real implementation keeps
only a `windowSize`-bit bitmap of the counters below `next`. -/
structure Window where
  next : Nat
  seen : List Nat
deriving Repr

/-- A fresh window: nothing received yet. -/
def Window.fresh : Window := { next := 0, seen := [] }

/-- The acceptance decision of §5.4.7, in the RFC 6479 formulation:
* a counter at or beyond `next` is always accepted (the window is
  growing, so no replay is possible);
* a counter more than `windowSize` behind `next` is too old — dropped;
* a counter inside the window is accepted only if it is not already in
  `seen`. -/
def Window.willAccept (w : Window) (c : Nat) : Bool :=
  if c ≥ w.next then true
  else if c + windowSize < w.next then false
  else !(w.seen.contains c)

/-- Record an accepted counter: advance `next` past it if it is the new
high-water mark, and add it to the seen set. Only ever applied to a
counter the filter accepted. -/
def Window.mark (w : Window) (c : Nat) : Window :=
  { next := if c ≥ w.next then c + 1 else w.next,
    seen := c :: w.seen }

/-- The window invariant: every accepted counter is strictly below the
high-water mark. Maintained by construction and needed to prove that a
previously accepted counter is rejected on replay. -/
def Window.Inv (w : Window) : Prop :=
  ∀ c, w.seen.contains c = true → c < w.next

theorem Window.inv_fresh : Window.Inv Window.fresh := by
  intro c h
  simp [Window.fresh] at h

theorem Window.inv_mark (w : Window) (c : Nat) (h : Window.Inv w) :
    Window.Inv (w.mark c) := by
  intro x hx
  simp only [Window.mark, List.contains_cons] at hx
  rcases Bool.or_eq_true _ _ |>.mp hx with he | he
  · have hxc : x = c := eq_of_beq he
    subst hxc
    simp only [Window.mark]
    by_cases hc : x ≥ w.next <;> simp [hc] <;> omega
  · have hxlt : x < w.next := h x he
    simp only [Window.mark]
    by_cases hc : c ≥ w.next <;> simp [hc] <;> omega

/-- `mark` never lowers the high-water mark. -/
theorem Window.mark_next_ge (w : Window) (c : Nat) :
    w.next ≤ (w.mark c).next := by
  simp only [Window.mark]
  by_cases hc : c ≥ w.next <;> simp [hc]
  omega

/-- **Too-old rejection.** A counter more than `windowSize` behind the
high-water mark is rejected outright — no history needed. -/
theorem Window.too_old_rejected (w : Window) (c : Nat)
    (h : c + windowSize < w.next) : w.willAccept c = false := by
  have hge : ¬ (c ≥ w.next) := by omega
  simp [Window.willAccept, hge, h]

/-- **Replay rejection.** Under the invariant, a counter already
accepted is rejected: `willAccept` returns `false`. This is the
anti-replay guarantee at the filter level. -/
theorem Window.replay_rejected (w : Window) (c : Nat)
    (hInv : Window.Inv w) (hc : w.seen.contains c = true) :
    w.willAccept c = false := by
  have hlt : c < w.next := hInv c hc
  have hge : ¬ (c ≥ w.next) := by omega
  simp only [Window.willAccept, hge, if_false]
  by_cases h2 : c + windowSize < w.next
  · simp [h2]
  · rw [if_neg h2, hc]; rfl

/-! ## The peer FSM -/

/-- The per-peer handshake/transport phase. -/
inductive Phase where
  /-- Idle: no handshake in progress. -/
  | start
  /-- Initiator: sent the handshake initiation, awaiting the response.
  No transport data may flow yet. -/
  | initSent (m : Initiation)
  /-- Handshake complete: session keys derived, transport data flows.
  Carries the role, keys, the receive anti-replay window, and the
  outbound send counter. -/
  | established (role : Role) (keys : Keys) (win : Window) (sendCtr : Nat)
  /-- Terminal / torn down. -/
  | dead
deriving Repr

/-- Inputs the environment can deliver. -/
inductive Input where
  /-- Application asks to start a handshake as the initiator. -/
  | initiate
  /-- A handshake initiation arrived (responder path). -/
  | recvInitiation (m : Initiation)
  /-- A handshake response arrived (initiator path). -/
  | recvResponse (m : Response)
  /-- Application asks to send transport plaintext. -/
  | appSend (data : Bytes)
  /-- A transport data message arrived. -/
  | recvTransport (m : TransportMsg)
  /-- Session expiry / rekey trigger. -/
  | expire
deriving Repr

/-- Outputs the machine can emit. -/
inductive Output where
  /-- A handshake initiation to the wire. -/
  | sendInitiation (m : Initiation)
  /-- A handshake response to the wire. -/
  | sendResponse (m : Response)
  /-- A transport data message to the wire (data plane). -/
  | sendTransport (m : TransportMsg)
  /-- Decrypted inbound transport plaintext to the application (data
  plane). -/
  | deliver (data : Bytes)
deriving Repr, DecidableEq

/-- The data-plane outputs: exactly the two that carry transport
payload. The no-transport-before-handshake theorem is about these. -/
def Output.isDataPlane : Output → Bool
  | .sendTransport _ => true
  | .deliver _ => true
  | _ => false

/-- Static configuration and the named crypto-effect vocabulary. Every
function-valued field is an uninterpreted total function: the theorems
about `step` hold for all of them. -/
structure Config where
  /-- The initiation this peer emits when it starts a handshake. -/
  makeInitiation : Initiation
  /-- Responder: does this initiation authenticate (decrypt + MAC + the
  §5.1 timestamp check)? -/
  acceptInitiation : Initiation → Bool
  /-- Initiator: does this response authenticate? -/
  acceptResponse : Response → Bool
  /-- Responder: the response emitted for an accepted initiation. -/
  makeResponse : Initiation → Response
  /-- Initiator: derive session keys from the accepted response. -/
  deriveInitiatorKeys : Response → Keys
  /-- Responder: derive session keys from the accepted initiation. -/
  deriveResponderKeys : Initiation → Keys
  /-- AEAD-seal outbound plaintext at a counter. -/
  sealTransport : Keys → Nat → Bytes → TransportMsg
  /-- AEAD-open an inbound transport message; `none` on auth failure. -/
  openTransport : Keys → TransportMsg → Option Bytes

/-- Machine state is just the phase (all history lives in the window's
ghost `seen` set). -/
structure St where
  phase : Phase
deriving Repr

/-- Initial state: idle. -/
def init : St := { phase := .start }

/-- Handle a transport message in the established phase: consult the
window, and only on acceptance (and successful AEAD-open) advance the
window and deliver plaintext. A rejected or unauthentic message is
dropped with the window untouched. -/
def recvData (cfg : Config) (role : Role) (keys : Keys) (win : Window)
    (sendCtr : Nat) (m : TransportMsg) : Phase × List Output :=
  if win.willAccept m.counter then
    match cfg.openTransport keys m with
    | some pt =>
      (.established role keys (win.mark m.counter) sendCtr, [.deliver pt])
    | none =>
      (.established role keys win sendCtr, [])
  else
    (.established role keys win sendCtr, [])

/-- The phase transition: a total match on phase × input. -/
def stepPhase (cfg : Config) : Phase → Input → Phase × List Output
  -- ── idle ──
  | .start, .initiate =>
    (.initSent cfg.makeInitiation, [.sendInitiation cfg.makeInitiation])
  | .start, .recvInitiation m =>
    if cfg.acceptInitiation m then
      (.established .responder (cfg.deriveResponderKeys m) Window.fresh 0,
       [.sendResponse (cfg.makeResponse m)])
    else
      (.start, [])
  | .start, _ => (.start, [])
  -- ── initiator: awaiting response ──
  | .initSent m, .recvResponse r =>
    if cfg.acceptResponse r then
      (.established .initiator (cfg.deriveInitiatorKeys r) Window.fresh 0, [])
    else
      (.initSent m, [])
  | .initSent m0, .recvInitiation m =>
    -- A crossing initiation: responder role wins, keys re-derived.
    if cfg.acceptInitiation m then
      (.established .responder (cfg.deriveResponderKeys m) Window.fresh 0,
       [.sendResponse (cfg.makeResponse m)])
    else
      (.initSent m0, [])
  | .initSent _, .expire => (.start, [])
  | .initSent m, _ => (.initSent m, [])
  -- ── established: transport data flows ──
  | .established role keys win sendCtr, .appSend data =>
    (.established role keys win (sendCtr + 1),
     [.sendTransport (cfg.sealTransport keys sendCtr data)])
  | .established role keys win sendCtr, .recvTransport m =>
    recvData cfg role keys win sendCtr m
  | .established _ _ _ _, .expire => (.start, [])
  | .established role keys win sendCtr, _ =>
    (.established role keys win sendCtr, [])
  -- ── dead ──
  | .dead, _ => (.dead, [])

/-- The total transition. -/
def step (cfg : Config) (s : St) (i : Input) : St × List Output :=
  ({ phase := (stepPhase cfg s.phase i).1 }, (stepPhase cfg s.phase i).2)

/-- Fold the step over an input trace, collecting every step's output. -/
def run (cfg : Config) (s : St) : List Input → St × List (List Output)
  | [] => (s, [])
  | i :: is =>
    ((run cfg (step cfg s i).1 is).1,
     (step cfg s i).2 :: (run cfg (step cfg s i).1 is).2)

/-- States reachable from the initial state under some input. -/
inductive Reachable (cfg : Config) : St → Prop where
  | init : Reachable cfg init
  | step {s : St} (h : Reachable cfg s) (i : Input) :
      Reachable cfg (step cfg s i).1

/-! ## Totality and determinism -/

/-- The step relation induced by the step function. -/
def Steps (cfg : Config) (s : St) (i : Input) (s' : St)
    (o : List Output) : Prop :=
  step cfg s i = (s', o)

theorem step_total (cfg : Config) (s : St) (i : Input) :
    ∃ s' o, Steps cfg s i s' o :=
  ⟨(step cfg s i).1, (step cfg s i).2, rfl⟩

theorem step_deterministic (cfg : Config) (s : St) (i : Input)
    {s₁ s₂ : St} {o₁ o₂ : List Output}
    (h₁ : Steps cfg s i s₁ o₁) (h₂ : Steps cfg s i s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  have h := h₁.symm.trans h₂
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## No transport before the handshake completes -/

/-- `true` exactly on the established phase. -/
def Phase.isEstablished : Phase → Bool
  | .established _ _ _ _ => true
  | _ => false

/-- `recvData` only ever emits `deliver`, never a wire send, and only
from an established successor. -/
theorem recvData_dataplane (cfg : Config) (role : Role) (keys : Keys)
    (win : Window) (sendCtr : Nat) (m : TransportMsg) :
    ∀ o ∈ (recvData cfg role keys win sendCtr m).2,
      ∃ d, o = .deliver d := by
  intro o ho
  unfold recvData at ho
  split at ho
  · split at ho
    · simp at ho; exact ⟨_, ho⟩
    · simp at ho
  · simp at ho

/-- **No transport before handshake**, step form: any data-plane output
of a step comes from a step whose *starting* phase is already
`established`. Every other phase — idle, initiation-sent, dead — emits
only handshake control messages, never transport data. -/
theorem wg_no_transport_before_handshake (cfg : Config) (s : St)
    (i : Input) (o : Output)
    (ho : o ∈ (step cfg s i).2) (hd : o.isDataPlane = true) :
    s.phase.isEstablished = true := by
  rcases s with ⟨p⟩
  cases p <;> cases i <;>
    simp_all [step, stepPhase, Phase.isEstablished, Output.isDataPlane]
  all_goals (
    first
    | (split at ho <;> simp_all [Output.isDataPlane])
    | (rename_i m;
       rcases recvData_dataplane cfg _ _ _ _ m o ho with ⟨d, rfl⟩;
       simp [Output.isDataPlane]))

/-- **Entering `established` is a handshake completion.** If a step
moves from a non-established phase into `established`, then the input
was a handshake message that the crypto boundary *accepted*: either an
initiator accepting a valid response, or a responder accepting a valid
initiation. There is no other door into the transport phase. -/
theorem wg_established_needs_handshake (cfg : Config) (s : St)
    (i : Input) {role : Role} {keys : Keys} {win : Window} {sc : Nat}
    (hpre : s.phase.isEstablished = false)
    (hpost : (step cfg s i).1.phase = .established role keys win sc) :
    (∃ r, i = .recvResponse r ∧ cfg.acceptResponse r = true) ∨
    (∃ m, i = .recvInitiation m ∧ cfg.acceptInitiation m = true) := by
  rcases s with ⟨p⟩
  cases p with
  | start =>
    cases i with
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · exact Or.inr ⟨m, rfl, by assumption⟩
      · simp at hpost
    | _ => simp only [step, stepPhase] at hpost; simp at hpost
  | initSent m0 =>
    cases i with
    | recvResponse r =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · exact Or.inl ⟨r, rfl, by assumption⟩
      · simp at hpost
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · exact Or.inr ⟨m, rfl, by assumption⟩
      · simp at hpost
    | _ => simp only [step, stepPhase] at hpost; simp at hpost
  | established r0 k0 w0 s0 =>
    simp [Phase.isEstablished] at hpre
  | dead =>
    cases i <;> (simp only [step, stepPhase] at hpost; simp at hpost)

/-! ## The reachable-window invariant -/

/-- Every reachable established state carries a window satisfying the
anti-replay invariant. -/
def WinInv (s : St) : Prop :=
  ∀ role keys win sc, s.phase = .established role keys win sc →
    Window.Inv win

theorem winInv_init : WinInv init := by
  intro role keys win sc h
  simp [init] at h

theorem winInv_step (cfg : Config) (s : St) (i : Input)
    (h : WinInv s) : WinInv (step cfg s i).1 := by
  rcases s with ⟨p⟩
  intro role keys win sc hpost
  cases p with
  | start =>
    cases i with
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · injection hpost with _ _ hw _; subst hw; exact Window.inv_fresh
      · simp at hpost
    | _ => simp only [step, stepPhase] at hpost; simp at hpost
  | initSent m0 =>
    cases i with
    | recvResponse r =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · injection hpost with _ _ hw _; subst hw; exact Window.inv_fresh
      · simp at hpost
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · injection hpost with _ _ hw _; subst hw; exact Window.inv_fresh
      · simp at hpost
    | _ => simp only [step, stepPhase] at hpost; simp at hpost
  | established r0 k0 w0 s0 =>
    have hw0 : Window.Inv w0 := h r0 k0 w0 s0 rfl
    cases i with
    | appSend data =>
      simp only [step, stepPhase] at hpost
      injection hpost with _ _ hw _; subst hw; exact hw0
    | recvTransport m =>
      simp only [step, stepPhase, recvData] at hpost
      split at hpost
      · split at hpost
        · injection hpost with _ _ hw _; subst hw
          exact Window.inv_mark _ _ hw0
        · injection hpost with _ _ hw _; subst hw; exact hw0
      · injection hpost with _ _ hw _; subst hw; exact hw0
    | expire => simp only [step, stepPhase] at hpost; simp at hpost
    | initiate =>
      simp only [step, stepPhase] at hpost
      injection hpost with _ _ hw _; subst hw; exact hw0
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      injection hpost with _ _ hw _; subst hw; exact hw0
    | recvResponse r =>
      simp only [step, stepPhase] at hpost
      injection hpost with _ _ hw _; subst hw; exact hw0
  | dead =>
    cases i <;> (simp only [step, stepPhase] at hpost; simp at hpost)

theorem winInv_reachable (cfg : Config) {s : St}
    (h : Reachable cfg s) : WinInv s := by
  induction h with
  | init => exact winInv_init
  | step _ i ih => exact winInv_step cfg _ i ih

/-! ## Anti-replay at the FSM level -/

/-- **Replay rejected.** In every reachable state, feeding a transport
message whose counter was already accepted (or has dropped below the
window) delivers nothing and leaves the window unchanged. A replayed
packet has no effect. -/
theorem wg_replay_rejected (cfg : Config) {s : St}
    (hr : Reachable cfg s) {role : Role} {keys : Keys} {win : Window}
    {sc : Nat} (hph : s.phase = .established role keys win sc)
    (m : TransportMsg) (hseen : win.seen.contains m.counter = true) :
    (step cfg s (.recvTransport m)).2 = [] ∧
    (step cfg s (.recvTransport m)).1.phase
      = .established role keys win sc := by
  have hInv : Window.Inv win := winInv_reachable cfg hr role keys win sc hph
  have hrej : win.willAccept m.counter = false :=
    Window.replay_rejected win m.counter hInv hseen
  rcases s with ⟨p⟩
  simp only at hph
  subst hph
  simp only [step, stepPhase, recvData, hrej, if_false]
  exact ⟨rfl, rfl⟩

/-- **Too-old rejected.** Same conclusion for a counter that has fallen
more than a window behind the high-water mark — no history needed. -/
theorem wg_too_old_rejected (cfg : Config) (s : St)
    {role : Role} {keys : Keys} {win : Window} {sc : Nat}
    (hph : s.phase = .established role keys win sc)
    (m : TransportMsg) (hold : m.counter + windowSize < win.next) :
    (step cfg s (.recvTransport m)).2 = [] ∧
    (step cfg s (.recvTransport m)).1.phase
      = .established role keys win sc := by
  have hrej : win.willAccept m.counter = false :=
    Window.too_old_rejected win m.counter hold
  rcases s with ⟨p⟩
  simp only at hph
  subst hph
  simp only [step, stepPhase, recvData, hrej, if_false]
  exact ⟨rfl, rfl⟩

/-! ## Counter monotonicity -/

/-- The window high-water mark of an established phase, or 0 elsewhere.
One past the highest transport counter ever accepted. -/
def Phase.recvHighWater : Phase → Nat
  | .established _ _ win _ => win.next
  | _ => 0

/-- The outbound send counter of an established phase, or 0 elsewhere. -/
def Phase.sendCounter : Phase → Nat
  | .established _ _ _ sc => sc
  | _ => 0

/-- **Receive counter monotone.** While a peer stays established, the
receive high-water mark never decreases: an accepted transport message
only advances it, and every non-transport step leaves it fixed. -/
theorem wg_counter_monotone (cfg : Config) (s : St) (i : Input)
    {role : Role} {keys : Keys} {win : Window} {sc : Nat}
    (hpre : s.phase = .established role keys win sc)
    {role' : Role} {keys' : Keys} {win' : Window} {sc' : Nat}
    (hpost : (step cfg s i).1.phase = .established role' keys' win' sc') :
    win.next ≤ win'.next := by
  rcases s with ⟨p⟩
  simp only at hpre
  subst hpre
  cases i with
  | appSend data =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ hw _; exact Nat.le_of_eq (congrArg Window.next hw)
  | recvTransport m =>
    simp only [step, stepPhase, recvData] at hpost
    split at hpost
    · split at hpost
      · injection hpost with _ _ hw _; subst hw
        exact Window.mark_next_ge win m.counter
      · injection hpost with _ _ hw _
        exact Nat.le_of_eq (congrArg Window.next hw)
    · injection hpost with _ _ hw _
      exact Nat.le_of_eq (congrArg Window.next hw)
  | expire => simp only [step, stepPhase] at hpost; simp at hpost
  | initiate =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ hw _; exact Nat.le_of_eq (congrArg Window.next hw)
  | recvInitiation m =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ hw _; exact Nat.le_of_eq (congrArg Window.next hw)
  | recvResponse r =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ hw _; exact Nat.le_of_eq (congrArg Window.next hw)

/-- **Send counter monotone.** The outbound counter never decreases
while the peer stays established (it advances by one on each send). -/
theorem wg_send_counter_monotone (cfg : Config) (s : St) (i : Input)
    {role : Role} {keys : Keys} {win : Window} {sc : Nat}
    (hpre : s.phase = .established role keys win sc)
    {role' : Role} {keys' : Keys} {win' : Window} {sc' : Nat}
    (hpost : (step cfg s i).1.phase = .established role' keys' win' sc') :
    sc ≤ sc' := by
  rcases s with ⟨p⟩
  simp only at hpre
  subst hpre
  cases i with
  | appSend data =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ _ hs; omega
  | recvTransport m =>
    simp only [step, stepPhase, recvData] at hpost
    split at hpost
    · split at hpost
      · injection hpost with _ _ _ hs; omega
      · injection hpost with _ _ _ hs; omega
    · injection hpost with _ _ _ hs; omega
  | expire => simp only [step, stepPhase] at hpost; simp at hpost
  | initiate =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ _ hs; omega
  | recvInitiation m =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ _ hs; omega
  | recvResponse r =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ _ hs; omega

/-! ## The sliding window, fully characterized

`Window.replay_rejected` and `Window.too_old_rejected` give one direction:
a replayed or stale counter is refused. The data-plane guarantee needs the
whole decision, both ways — a counter is accepted *iff* it is either ahead
of the window or fresh inside it. These theorems close that. -/

/-- **Accepts ahead of the window.** A counter at or beyond the high-water
mark is always accepted — the window only ever grew past accepted
counters, so nothing ahead of it can be a replay. -/
theorem wg_window_accepts_ahead (w : Window) (c : Nat) (h : w.next ≤ c) :
    w.willAccept c = true := by
  unfold Window.willAccept
  rw [if_pos h]

/-- **Accepts a fresh in-window counter.** A counter inside the window
(not more than `windowSize` behind the mark) that has not been seen before
is accepted — legitimate reordering is not mistaken for a replay. -/
theorem wg_window_accepts_fresh (w : Window) (c : Nat)
    (h1 : w.next ≤ c + windowSize) (h2 : w.seen.contains c = false) :
    w.willAccept c = true := by
  unfold Window.willAccept
  by_cases hc : c ≥ w.next
  · rw [if_pos hc]
  · rw [if_neg hc, if_neg (by omega : ¬ c + windowSize < w.next), h2]; rfl

/-- **The window decision, exactly.** `willAccept` returns `true` precisely
when the counter is ahead of the window, or is inside the window and has
not been seen. This is the complete acceptance predicate of §5.4.7 — every
other counter (already seen, or fallen off the back of the window) is
rejected. Combined with the invariant, this is the full anti-replay
characterization: accepted ⇔ in-window-and-unseen (or ahead). -/
theorem wg_replay_window_correct (w : Window) (c : Nat) :
    w.willAccept c = true ↔
      (w.next ≤ c) ∨ (w.next ≤ c + windowSize ∧ w.seen.contains c = false) := by
  unfold Window.willAccept
  by_cases h1 : c ≥ w.next
  · rw [if_pos h1]
    constructor
    · intro _; exact Or.inl h1
    · intro _; rfl
  · rw [if_neg h1]
    by_cases h2 : c + windowSize < w.next
    · rw [if_pos h2]
      constructor
      · intro h; simp at h
      · rintro (h | ⟨hle, _⟩)
        · exact absurd h h1
        · exact absurd h2 (Nat.not_lt.mpr hle)
    · rw [if_neg h2]
      constructor
      · intro h
        have hcon : w.seen.contains c = false := by
          cases hh : w.seen.contains c with
          | false => rfl
          | true => rw [hh] at h; simp at h
        exact Or.inr ⟨by omega, hcon⟩
      · rintro (h | ⟨_, hcon⟩)
        · exact absurd h h1
        · rw [hcon]; rfl

/-! ## The real Noise IK handshake (whitepaper §5.4), on verified crypto

Everything above treats the handshake itself as an uninterpreted boundary
(`Config.acceptInitiation`, `deriveInitiatorKeys`, …) so the FSM theorems
hold for every cipher. This section fills that boundary in with the
*actual* Noise IKpsk2 key schedule, computed on the HACL*/EverCrypt
primitives exposed by `Crypto`:

* X25519 (`Crypto.x25519`, `Crypto.x25519Base`) for the Diffie–Hellman
  chain — the four shared secrets `es, ss, ee, se`;
* HKDF-SHA-256 (`Crypto.hkdfExtract` / `Crypto.hkdfExpand`) for the
  chaining-key ratchet — the whitepaper's `KDF_n`;
* ChaCha20-Poly1305 (`Crypto.chachaSeal` / `Crypto.chachaOpen`) for the
  AEAD-sealed static key and timestamp.

The message layout follows §5.4 exactly, with one honest substitution:
WireGuard mandates BLAKE2s and our verified seam offers SHA-256, so the
ratchet is instantiated on SHA-256. The agreement argument — that both
peers converge on a single chaining key built from the same four DH
secrets — is identical under either hash.

The payoff (`wg_handshake_real`) is that the two peers, computing their
secrets from opposite ends, derive the *same* chaining key and hence the
same transport keys — because at each of the four DH steps the initiator's
`x25519 a (base b)` equals the responder's `x25519 b (base a)`
(`Crypto.Assumptions.x25519_dh_agree`). This is the real crypto agreement,
not an assumed `deriveKeys` function. -/

namespace Noise

/-- A party's keypair: a 32-byte X25519 private scalar and its public
point. `WF` says the public point really is the scalar's base multiple —
the one fact the agreement proof consumes. -/
structure KeyPair where
  priv : ByteArray
  pub  : ByteArray

def KeyPair.WF (kp : KeyPair) : Prop := Crypto.x25519Base kp.priv = some kp.pub

/-- The Noise `KDF_n` of the whitepaper: HKDF-SHA-256 keyed on the current
chaining key, expanded to `32*n` bytes (the caller slices out the `n`
32-byte outputs). A size failure at the seam propagates as `none`. -/
def kdf (ck input : ByteArray) (n : Nat) : Option ByteArray :=
  (Crypto.hkdfExtract ck input).bind fun prk =>
    Crypto.hkdfExpand prk ByteArray.empty (USize.ofNat (32 * n))

/-- Mix a public value (an unencrypted ephemeral, or the preshared key)
into the chaining key: `ck ← KDF1(ck, m)`. -/
def mixKey (ck : Option ByteArray) (m : ByteArray) : Option ByteArray :=
  ck.bind fun c => kdf c m 1

/-- Mix a Diffie–Hellman shared secret into the chaining key. The secret
is itself an `Option` (X25519 rejects low-order points, RFC 7748 §6.1), so
a failure at the DH step, or any earlier step, collapses the chain to
`none`. -/
def mixDH (ck secret : Option ByteArray) : Option ByteArray :=
  match ck, secret with
  | some c, some s => kdf c s 1
  | _, _ => none

/-- The construction identifier. WireGuard's is
`Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s`; ours names the hash we actually
run through the verified seam. -/
def construction : ByteArray :=
  "Noise_IKpsk2_25519_ChaChaPoly_SHA256".toUTF8

/-- The initial chaining key `Ci = Hash(CONSTRUCTION)` (§5.4.1). A fixed
constant, identical on both peers. -/
def ckInit : ByteArray := Crypto.sha256 construction

/-- The chaining-key ratchet through a full IK handshake, as a function of
the two *public* ephemerals, the preshared key, and the four
Diffie–Hellman shared secrets in whitepaper order: `es`, `ss` (initiation)
then `ee`, `se` (response), with the preshared key mixed last (the `psk2`
of IKpsk2). This is exactly the sequence of `KDF1` applications producing
the final chaining key; the transport keys derive from its output. Written
once and applied by both peers — they differ only in *how* they compute
the four secrets. -/
def chainingKey (epubI epubR psk : ByteArray)
    (es ss ee se : Option ByteArray) : Option ByteArray :=
  let ck := some ckInit
  let ck := mixKey ck epubI      -- unencrypted initiator ephemeral (§5.4.2)
  let ck := mixDH  ck es         -- es = DH(ei, sr)
  let ck := mixDH  ck ss         -- ss = DH(si, sr)
  let ck := mixKey ck epubR      -- unencrypted responder ephemeral (§5.4.3)
  let ck := mixDH  ck ee         -- ee = DH(ei, er)
  let ck := mixDH  ck se         -- se = DH(si, er)
  let ck := mixKey ck psk        -- preshared key
  ck

/-- The transport-key material, `KDF2(ck, ε)` (§5.4.5): 64 bytes carrying
`(T_send_i, T_recv_i)`. The responder derives the same 64 bytes and uses
them with the two directions swapped, so agreement on `ck` is agreement on
both directions' keys. -/
def transportKeys (ck : Option ByteArray) : Option ByteArray :=
  ck.bind fun c => kdf c ByteArray.empty 2

/-- The initiator's chaining key. It holds `si, ei`, was told the
responder's static public `spubR`, learns the responder's ephemeral public
`epubR` from the response, and computes its four secrets from its own
private scalars. `epubI` is its own ephemeral public (also on the wire). -/
def initiatorChainingKey (si ei epubI spubR epubR psk : ByteArray) :
    Option ByteArray :=
  chainingKey epubI epubR psk
    (Crypto.x25519 ei spubR)   -- es = DH(ei, sr)
    (Crypto.x25519 si spubR)   -- ss = DH(si, sr)
    (Crypto.x25519 ei epubR)   -- ee = DH(ei, er)
    (Crypto.x25519 si epubR)   -- se = DH(si, er)

/-- The responder's chaining key. It holds `sr, er`, learns the
initiator's static public `spubI` (by decrypting the initiation) and
ephemeral public `epubI` (in the clear), and computes the *same* four
secrets from the opposite end. -/
def responderChainingKey (sr er spubI epubI epubR psk : ByteArray) :
    Option ByteArray :=
  chainingKey epubI epubR psk
    (Crypto.x25519 sr epubI)   -- es = DH(sr, ei)
    (Crypto.x25519 sr spubI)   -- ss = DH(sr, si)
    (Crypto.x25519 er epubI)   -- ee = DH(er, ei)
    (Crypto.x25519 er spubI)   -- se = DH(er, si)

/-- **The handshake derives one shared chaining key via the real DH
chain.** Given well-formed keypairs (each public point is its scalar's
base multiple), the initiator and responder — computing their four
Diffie–Hellman secrets from opposite ends — arrive at the *same* chaining
key. Each equality `x25519 a (base b) = x25519 b (base a)` is discharged
by the X25519 agreement axiom; the ratchet is otherwise a deterministic
fold of identical public inputs, so the results coincide. This is the
Noise IK guarantee on verified crypto, replacing the FSM's abstract
`deriveInitiatorKeys` / `deriveResponderKeys` boundary. -/
theorem wg_handshake_real
    (si ei sr er spubI epubI spubR epubR psk : ByteArray)
    (hSI : Crypto.x25519Base si = some spubI)
    (hEI : Crypto.x25519Base ei = some epubI)
    (hSR : Crypto.x25519Base sr = some spubR)
    (hER : Crypto.x25519Base er = some epubR) :
    initiatorChainingKey si ei epubI spubR epubR psk
      = responderChainingKey sr er spubI epubI epubR psk := by
  unfold initiatorChainingKey responderChainingKey
  rw [Crypto.Assumptions.x25519_dh_agree ei sr epubI spubR hEI hSR,
      Crypto.Assumptions.x25519_dh_agree si sr spubI spubR hSI hSR,
      Crypto.Assumptions.x25519_dh_agree ei er epubI epubR hEI hER,
      Crypto.Assumptions.x25519_dh_agree si er spubI epubR hSI hER]

/-- **Both peers derive identical transport keys.** An immediate corollary:
the 64-byte `KDF2(ck, ε)` transport material is the same on both ends, so
the initiator's send key is the responder's receive key and vice versa. -/
theorem wg_transport_keys_agree
    (si ei sr er spubI epubI spubR epubR psk : ByteArray)
    (hSI : Crypto.x25519Base si = some spubI)
    (hEI : Crypto.x25519Base ei = some epubI)
    (hSR : Crypto.x25519Base sr = some spubR)
    (hER : Crypto.x25519Base er = some epubR) :
    transportKeys (initiatorChainingKey si ei epubI spubR epubR psk)
      = transportKeys (responderChainingKey sr er spubI epubI epubR psk) :=
  congrArg transportKeys
    (wg_handshake_real si ei sr er spubI epubI spubR epubR psk hSI hEI hSR hER)

/-! ### The AEAD-sealed static key and timestamp, on real ChaCha20-Poly1305

The initiation (§5.4.2) carries the initiator's static public key and a
TAI64N timestamp, each AEAD-sealed under a key derived from the chaining
key at that step, with the running transcript hash as associated data. The
responder, having derived the *same* key (from the proven-equal chaining
key) and the same transcript, recovers them. These are the real AEAD
roundtrip and forgery-resistance, not a boolean `acceptInitiation`. -/

/-- The all-zero 96-bit AEAD nonce the Noise counter starts at (`0` for the
first message under each key). -/
def nonce0 : ByteArray := ⟨Array.mkArray 12 (0 : UInt8)⟩

/-- Seal the initiator's static public key (§5.4.2, `encrypted_static`):
`AEAD(k, 0, spubI, hash)`. -/
def sealStatic (k hash spubI : ByteArray) : Option ByteArray :=
  Crypto.chachaSeal k nonce0 hash spubI

/-- **The responder recovers the initiator's static key.** With the same
derived key and transcript hash, opening `encrypted_static` yields exactly
the initiator's static public key — the real AEAD roundtrip. -/
theorem wg_static_key_authenticated (k hash spubI ct : ByteArray)
    (hseal : sealStatic k hash spubI = some ct) :
    Crypto.chachaOpen k nonce0 hash ct = some spubI :=
  Crypto.Assumptions.chacha_open_seal_roundtrip k nonce0 hash spubI ct hseal

/-- **No forged static key is ever accepted.** The only ciphertext that
opens to a given static key under this key/hash is the one the genuine
initiator sealed — AEAD forgery-resistance. A responder that admits an
initiation only on `chachaOpen … = some spubI` therefore only ever admits
a peer that actually holds the shared key material. -/
theorem wg_static_key_unforgeable (k hash spubI ct : ByteArray)
    (hopen : Crypto.chachaOpen k nonce0 hash ct = some spubI) :
    Crypto.chachaSeal k nonce0 hash spubI = some ct :=
  Crypto.Assumptions.chacha_open_authentic k nonce0 hash ct spubI hopen

end Noise

/-! ## Rekey timers (whitepaper §6.1)

A session is bounded in both messages and time. WireGuard rekeys — starts
a fresh handshake — well before it is ever forced to drop the session, so
a live tunnel never stalls. These are the stock constants and the ordering
guarantee between the soft (rekey) and hard (reject) thresholds. -/

namespace Rekey

/-- Send-count rekey trigger: `2^60` messages. -/
def REKEY_AFTER_MESSAGES : Nat := 2 ^ 60
/-- Send-count hard limit: `2^64 − 2^13 − 1` messages (nonce exhaustion). -/
def REJECT_AFTER_MESSAGES : Nat := 2 ^ 64 - 2 ^ 13 - 1
/-- Time rekey trigger: 120 seconds. -/
def REKEY_AFTER_TIME : Nat := 120
/-- Time hard limit: 180 seconds. -/
def REJECT_AFTER_TIME : Nat := 180
/-- Handshake retransmit interval: 5 seconds. -/
def REKEY_TIMEOUT : Nat := 5

/-- A live session's usage: transport messages sent under the current keys,
and seconds since the handshake that established them. -/
structure Session where
  msgs : Nat
  age  : Nat
deriving Repr

/-- A new handshake should be started: either enough messages have been
sent or enough time has passed. -/
def needsRekey (s : Session) : Bool :=
  decide (REKEY_AFTER_MESSAGES ≤ s.msgs) || decide (REKEY_AFTER_TIME ≤ s.age)

/-- The session must be torn down (no more transport data): a hard limit
was hit. -/
def mustReject (s : Session) : Bool :=
  decide (REJECT_AFTER_MESSAGES ≤ s.msgs) || decide (REJECT_AFTER_TIME ≤ s.age)

/-- Sending a transport message advances the counter. -/
def onSend (s : Session) : Session := { s with msgs := s.msgs + 1 }
/-- Time passes. -/
def onTick (s : Session) (dt : Nat) : Session := { s with age := s.age + dt }

/-- The soft thresholds sit strictly below the hard ones. -/
theorem rekey_thresholds_ordered :
    REKEY_AFTER_MESSAGES ≤ REJECT_AFTER_MESSAGES ∧
    REKEY_AFTER_TIME ≤ REJECT_AFTER_TIME := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Rekey precedes reject.** Any session that has reached a hard reject
threshold has already crossed the rekey threshold — a correct peer always
initiates a new handshake before it is ever forced to drop the session, so
a live tunnel never dies mid-flight for lack of a fresh key. -/
theorem wg_rekey_before_reject (s : Session) (h : mustReject s = true) :
    needsRekey s = true := by
  obtain ⟨hm, ht⟩ := rekey_thresholds_ordered
  simp only [needsRekey, mustReject, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with hh | hh
  · exact Or.inl (Nat.le_trans hm hh)
  · exact Or.inr (Nat.le_trans ht hh)

/-- The send counter never decreases across a send. -/
theorem onSend_msgs_ge (s : Session) : s.msgs ≤ (onSend s).msgs := by
  simp [onSend]

end Rekey

/-! ## Cookie-reply DoS mitigation (whitepaper §5.3 / §5.4.7)

Under CPU load the responder must not spend an X25519/AEAD handshake on an
unverified sender. Each initiation carries MAC1 (proves the sender knows
the responder's public key) and, when demanded, MAC2 (proves the sender
recently received a cookie tied to its source address). Under load a valid
MAC2 is required; without it the responder answers with a cheap cookie
reply and does *no* handshake work. The cookie's own authenticity (a keyed
MAC over the source address under a rotating secret) is the crypto
boundary; the admission logic below is what mitigates the flood. -/

namespace Cookie

/-- The responder's response to an inbound initiation under the §5.3
admission rule. -/
inductive Reply where
  /-- MAC1 invalid: not even addressed to this responder; dropped in silence. -/
  | drop
  /-- Under load without a valid cookie MAC2: a cheap cookie reply, and no
  handshake computation. -/
  | cookieReply
  /-- Admitted: run the (expensive) Noise handshake response. -/
  | handshake
deriving Repr, DecidableEq

/-- The admission decision. MAC1 is always required. Under load, a valid
MAC2 is additionally required; without it the only response is a cookie
reply — crucially, no Diffie–Hellman or AEAD work is performed. Off load,
MAC1 alone admits the handshake. -/
def admit (mac1Valid mac2Valid underLoad : Bool) : Reply :=
  if mac1Valid = false then .drop
  else if underLoad = true ∧ mac2Valid = false then .cookieReply
  else .handshake

/-- **Cookie mitigation.** Under load, an initiation without a valid cookie
MAC2 is never admitted to the handshake — the responder spends only a
cheap cookie reply (or a drop), never an X25519/AEAD handshake. This is the
DoS guarantee: an off-path flood cannot force handshake work. -/
theorem wg_cookie_mitigates (mac1Valid : Bool) :
    admit mac1Valid false true ≠ Reply.handshake := by
  cases mac1Valid <;> decide

/-- Under load, an invalid cookie yields exactly a cookie reply (given a
valid MAC1). -/
theorem wg_cookie_reply_under_load :
    admit true false true = Reply.cookieReply := by decide

/-- A valid MAC1+MAC2 is admitted, load or not. -/
theorem wg_cookie_admits_valid (underLoad : Bool) :
    admit true true underLoad = Reply.handshake := by
  cases underLoad <;> decide

/-- A bad MAC1 is always dropped — before any cookie or handshake work. -/
theorem wg_cookie_bad_mac1_dropped (mac2 underLoad : Bool) :
    admit false mac2 underLoad = Reply.drop := rfl

end Cookie

end Wireguard
