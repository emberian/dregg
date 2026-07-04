import Tls.Basic

/-!
# TLS record/handshake machine — the sans-IO step

`step cfg s i` is total and pure. Record protection is behind the named
crypto fields of `Config`; the machine's job is the lifecycle: who
currently owns the record layer (the handshake engine, the userspace
record engine, or the kernel), what may be emitted from each phase, and
how the connection dies.

Structure:

* `hsDrive` — drive the handshake engine on the accumulated ciphertext
  (shared by `accum` and `handshaking`); early (0.5-RTT) plaintext
  surfaces here, gated by `earlyIf`.
* `finishHs` — handshake completion: route to the offload window
  (`ktls` policy) or to the userspace record path.
* `recDrive` — the established userspace record path (AEAD-open,
  close_notify detection).
* `stepPhase` / `step` — the total transition; `run` folds it over an
  input trace; `Reachable` is the induced reachability predicate.
-/

namespace Tls

/-- Emit a wire send only when nonempty. -/
def sendIf (b : Bytes) : List Output :=
  if b.isEmpty then [] else [.send b]

/-- Deliver decrypted plaintext only when nonempty. -/
def deliverIf (b : Bytes) : List Output :=
  if b.isEmpty then [] else [.deliverPlain b]

/-- Plaintext write on the offloaded socket, only when nonempty. -/
def sendPlainIf (b : Bytes) : List Output :=
  if b.isEmpty then [] else [.sendPlain b]

/-- Early (0.5-RTT) plaintext: delivered **only** under the explicit
acceptance flag (and only when nonempty). Unaccepted early data is
dropped here — it reaches no other output. -/
def earlyIf (cfg : Config) (b : Bytes) : List Output :=
  if cfg.earlyDataAccepted && !b.isEmpty then [.deliverEarly b] else []

/-- Handshake completion: route to the offload window or to the
userspace record path, per policy. `rest` is the unconsumed
ciphertext. -/
def finishHs (cfg : Config) (alpn : Alpn) (rc : RecConn) (rest : Bytes)
    (snd early : Bytes) : Phase × Eff :=
  if cfg.ktls then
    (.offloadAttach alpn rc rest [],
     { out := sendIf snd ++ earlyIf cfg early ++ [.attachUlp] })
  else
    (.estabUser alpn rc rest,
     { out := sendIf snd ++ earlyIf cfg early })

/-- Drive the handshake engine on the accumulated ciphertext. `stay` is
the phase to remain in while no complete record is available (`accum`
stays `accum`, `handshaking` stays `handshaking`). -/
def hsDrive (cfg : Config) (hs : HsConn) (buf : Bytes)
    (stay : HsConn → Bytes → Phase) : Phase × Eff :=
  match cfg.hsFeed hs buf with
  | .insufficient => (stay hs buf, {})
  | .more hs' n snd early =>
    (.handshaking hs' (buf.drop n),
     { out := sendIf snd ++ earlyIf cfg early })
  | .done rc n snd alpn early =>
    finishHs cfg alpn rc (buf.drop n) snd early
  | .fail => (.closed, { out := [.send cfg.fatalAlert, .close] })

/-- Feed accumulated ciphertext to the established userspace record
path. -/
def recDrive (cfg : Config) (alpn : Alpn) (rc : RecConn) (buf : Bytes) :
    Phase × Eff :=
  match cfg.recOpen rc buf with
  | .more rc' n plain =>
    (.estabUser alpn rc' (buf.drop n),
     { out := deliverIf plain, uses := [rc] })
  | .closeNotify _ plain =>
    (.closing,
     { out := deliverIf plain ++ [.send (cfg.recCloseNotify rc)],
       uses := [rc] })
  | .fail =>
    (.closed, { out := [.send cfg.fatalAlert, .close], uses := [rc] })

/-- The phase transition: a total match on phase × input. -/
def stepPhase (cfg : Config) : Phase → Input → Phase × Eff
  -- ── accumulating ciphertext (no complete record yet) ──
  | .accum hs buf, .bytesReceived d => hsDrive cfg hs (buf ++ d) .accum
  | .accum _ _, .closeRequested => (.closed, { out := [.close] })
  | .accum _ _, .peerClosed => (.closed, { out := [.close] })
  | .accum hs buf, _ => (.accum hs buf, {})
  -- ── handshake in progress ──
  | .handshaking hs buf, .bytesReceived d =>
    hsDrive cfg hs (buf ++ d) .handshaking
  | .handshaking _ _, .closeRequested => (.closed, { out := [.close] })
  | .handshaking _ _, .peerClosed => (.closed, { out := [.close] })
  | .handshaking hs buf, _ => (.handshaking hs buf, {})
  -- ── established, userspace record path ──
  | .estabUser alpn rc buf, .bytesReceived d =>
    recDrive cfg alpn rc (buf ++ d)
  | .estabUser alpn rc buf, .appData d =>
    (.estabUser alpn (cfg.recSeal rc d).1 buf,
     { out := [.send (cfg.recSeal rc d).2], uses := [rc] })
  | .estabUser _ rc _, .closeRequested =>
    (.closing, { out := [.send (cfg.recCloseNotify rc)], uses := [rc] })
  | .estabUser _ _ _, .peerClosed => (.closed, { out := [.close] })
  | .estabUser alpn rc buf, _ => (.estabUser alpn rc buf, {})
  -- ── offload window: ULP attach pending (connection still whole) ──
  | .offloadAttach alpn rc _ pend, .ulpAttached =>
    -- The consume-and-vanish edge: extract the secrets, destroy the
    -- userspace connection, start the TX install. Leftover ciphertext
    -- is surrendered to the kernel along with the receive direction.
    (.installingTx alpn (cfg.extractSecrets rc).rx pend,
     { out := [.installTx (cfg.extractSecrets rc).tx],
       uses := [rc], consumes := [rc] })
  | .offloadAttach alpn rc buf pend, .ulpUnavailable =>
    -- Fallback: the connection was never consumed; parked plaintext
    -- flushes through the userspace seal path.
    (.estabUser alpn (cfg.recSeal rc pend).1 buf,
     { out := sendIf (cfg.recSeal rc pend).2, uses := [rc] })
  | .offloadAttach _ _ _ _, .installFailed =>
    -- Hard attach error: teardown. The connection is dropped
    -- unconsumed; parked plaintext is discarded, never sent.
    (.closed, { out := [.close] })
  | .offloadAttach alpn rc buf pend, .bytesReceived d =>
    (.offloadAttach alpn rc (buf ++ d) pend, {})
  | .offloadAttach alpn rc buf pend, .appData d =>
    (.offloadAttach alpn rc buf (pend ++ d), {})
  | .offloadAttach _ rc _ _, .closeRequested =>
    (.closing, { out := [.send (cfg.recCloseNotify rc)], uses := [rc] })
  | .offloadAttach _ _ _ _, .peerClosed => (.closed, { out := [.close] })
  | .offloadAttach alpn rc buf pend, _ =>
    (.offloadAttach alpn rc buf pend, {})
  -- ── offload window: TX install in flight (secrets extracted) ──
  | .installingTx alpn rx pend, .installOk =>
    (.installingRx alpn pend, { out := [.installRx rx] })
  | .installingTx _ _ _, .installFailed => (.closed, { out := [.close] })
  | .installingTx alpn rx pend, .appData d =>
    (.installingTx alpn rx (pend ++ d), {})
  | .installingTx _ _ _, .closeRequested => (.closed, { out := [.close] })
  | .installingTx _ _ _, .peerClosed => (.closed, { out := [.close] })
  | .installingTx alpn rx pend, _ => (.installingTx alpn rx pend, {})
  -- ── offload window: RX install in flight — half-configured socket ──
  | .installingRx alpn pend, .installOk =>
    -- Fully configured: the kernel owns the record layer from here;
    -- parked plaintext flushes (the kernel seals it).
    (.estabOffload alpn, { out := sendPlainIf pend })
  | .installingRx _ _, .installFailed =>
    -- THE half-configured teardown edge: immediate close and nothing
    -- else — in particular the parked plaintext is dropped, not sent.
    (.closed, { out := [.close] })
  | .installingRx alpn pend, .appData d =>
    (.installingRx alpn (pend ++ d), {})
  | .installingRx _ _, .closeRequested => (.closed, { out := [.close] })
  | .installingRx _ _, .peerClosed => (.closed, { out := [.close] })
  | .installingRx alpn pend, _ => (.installingRx alpn pend, {})
  -- ── fully offloaded: kernel record layer ──
  | .estabOffload alpn, .bytesReceived d =>
    (.estabOffload alpn, { out := deliverIf d })
  | .estabOffload alpn, .appData d =>
    (.estabOffload alpn, { out := sendPlainIf d })
  | .estabOffload _, .closeRequested => (.closed, { out := [.close] })
  | .estabOffload _, .peerClosed => (.closed, { out := [.close] })
  | .estabOffload alpn, _ => (.estabOffload alpn, {})
  -- ── closing: draining the send path ──
  | .closing, .sendDrained => (.closed, { out := [.close] })
  | .closing, .peerClosed => (.closed, { out := [.close] })
  | .closing, _ => (.closing, {})
  -- ── closed: silent and absorbing ──
  | .closed, _ => (.closed, {})

/-- The top-level total transition: the phase steps, the ghost
consumed-set accumulates. -/
def step (cfg : Config) (s : St) (i : Input) : St × Eff :=
  ({ phase := (stepPhase cfg s.phase i).1,
     consumed := s.consumed ++ (stepPhase cfg s.phase i).2.consumes },
   (stepPhase cfg s.phase i).2)

/-- The step relation induced by the step function. -/
def Steps (cfg : Config) (s : St) (i : Input) (s' : St) (e : Eff) :
    Prop :=
  step cfg s i = (s', e)

/-- Fold the step over an input trace, collecting every step's effect. -/
def run (cfg : Config) (s : St) : List Input → St × List Eff
  | [] => (s, [])
  | i :: is =>
    ((run cfg (step cfg s i).1 is).1,
     (step cfg s i).2 :: (run cfg (step cfg s i).1 is).2)

/-- States reachable from the initial state. -/
inductive Reachable (cfg : Config) : St → Prop where
  | init : Reachable cfg (init cfg)
  | step {s : St} (hs : Reachable cfg s) (i : Input) :
      Reachable cfg (Tls.step cfg s i).1

end Tls
