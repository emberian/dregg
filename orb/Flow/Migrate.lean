/-
Migrate — connection-migration eligibility and the snapshot schema.

Live connections can be handed from one reactor shard to another — but
only from *quiescent* states. Eligibility is deliberately strict, and the
rules are transcribed as data, not invented:

  * HTTP/1 connections (plain or TLS) migrate only with an **empty receive
    accumulation** — a connection holding partially-received bytes is
    mid-request and stays put.
  * HTTP/2 connections migrate only with **no active streams and no
    pending per-stream state**.
  * Everything else — mid-handshake, WebSocket, tunnel, relay,
    intercepting-proxy sessions, any protocol state outside the four named
    classes — is **refused**.
  * Independently of protocol state, a connection is refused while any
    in-flight work is attached: request-body streams (plain or chunked),
    proxied body forwarding, an active upstream request, a streaming
    response, pending (send-blocked) outbound data, a server-sent-events
    teardown, or a forward-proxy role.

Eligibility is a **decidable predicate** over `ConnView`, a minimal
interface deliberately independent of the full connection FSM: exactly the
fields the migration decision reads, nothing else. `decide` closes
concrete instances.

The snapshot schema is the second half: `extract` refuses ineligible
connections (`extract_refuses_ineligible`) and succeeds on every eligible
one (`extract_eligible`); `inject` reconstructs the connection on the
adopting shard. The round-trip theorems are the schema-adequacy facts:

    inject_extract : inject ∘ extract = id  on eligible states
    extract_inject : extract ∘ inject = id  on snapshots

— extraction captures *everything* an eligible connection is (nothing is
dropped on the wire between shards), and adoption lands in an eligible
state carrying the *exact* session payload (the abstract `σ` — session
keys and sequence numbers ride the schema opaquely and round-trip
unchanged; their internal structure is the encryption layer's contract,
axiomatized here as the type parameter). -/

namespace Flow

/-- Protocol classification, as the migration decision sees it: the four
migratable classes carry the quiescence-relevant counters; everything else
collapses to `other` (never migratable). -/
inductive ProtoClass where
  /-- Plaintext HTTP/1 with `recvLen` accumulated request bytes. -/
  | plainH1 (recvLen : Nat)
  /-- TLS HTTP/1 with `recvLen` accumulated plaintext request bytes. -/
  | tlsH1 (recvLen : Nat)
  /-- TLS HTTP/2 with `activeStreams` open streams and `pendingStreams`
  per-stream state entries. -/
  | tlsH2 (activeStreams pendingStreams : Nat)
  /-- Plaintext-framed HTTP/2 (kernel-offloaded record layer). -/
  | plainH2 (activeStreams pendingStreams : Nat)
  /-- Any other protocol state: handshaking, WebSocket, tunnel, relay,
  SOCKS, … Never migratable. -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- Protocol-level quiescence: idle H1 (empty accumulation) or idle H2
(no streams). `other` is never idle *for migration purposes*. -/
def ProtoClass.idle : ProtoClass → Prop
  | .plainH1 n => n = 0
  | .tlsH1 n => n = 0
  | .tlsH2 a p => a = 0 ∧ p = 0
  | .plainH2 a p => a = 0 ∧ p = 0
  | .other => False

instance : (p : ProtoClass) → Decidable p.idle := by
  intro p
  cases p <;> (simp only [ProtoClass.idle]; infer_instance)

/-- The minimal state interface the migration decision reads. One Boolean
per kind of in-flight attachment; each `true` is an independent refusal
reason. -/
structure ConnView where
  /-- Protocol classification (with quiescence counters). -/
  protocol : ProtoClass
  /-- An in-flight request-body stream. -/
  bodyStream : Bool
  /-- An in-flight chunked request-body stream. -/
  chunkedBodyStream : Bool
  /-- Proxied request-body forwarding in flight. -/
  proxyBodyForward : Bool
  /-- An active upstream (reverse-proxy) request awaiting its response. -/
  upstreamGuard : Bool
  /-- An upstream response currently streaming back to the client. -/
  upstreamResponseStreaming : Bool
  /-- An upstream response send in progress. -/
  upstreamResponseSend : Bool
  /-- A streaming response (application handler, CGI, event stream). -/
  streamingResponse : Bool
  /-- Send-blocked outbound data queued for this socket (the send-path
  remainder of the flow-control machine). -/
  sendPending : Bool
  /-- An event-stream teardown in progress. -/
  sseShutdown : Bool
  /-- The connection serves a forward-proxy role. -/
  forwardProxy : Bool
  /-- The connection is an intercepting-proxy (re-terminated TLS) session. -/
  mitm : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Any in-flight attachment at all? -/
def ConnView.busy (c : ConnView) : Bool :=
  c.bodyStream || c.chunkedBodyStream || c.proxyBodyForward ||
  c.upstreamGuard || c.upstreamResponseStreaming || c.upstreamResponseSend ||
  c.streamingResponse || c.sendPending || c.sseShutdown ||
  c.forwardProxy || c.mitm

/-- **Migration eligibility**: no in-flight attachments, and the protocol
state is idle. Decidable — `decide` settles any concrete view. -/
def ConnView.Eligible (c : ConnView) : Prop :=
  c.busy = false ∧ c.protocol.idle

instance : DecidablePred ConnView.Eligible := fun c =>
  inferInstanceAs (Decidable (c.busy = false ∧ c.protocol.idle))

/-- An idle plaintext H1 connection with nothing attached is eligible —
the positive witness that the predicate is satisfiable. -/
example : ConnView.Eligible
    ⟨.plainH1 0, false, false, false, false, false, false,
     false, false, false, false, false⟩ := by decide

/-- A single accumulated byte refuses an otherwise idle H1 connection. -/
example : ¬ ConnView.Eligible
    ⟨.plainH1 1, false, false, false, false, false, false,
     false, false, false, false, false⟩ := by decide

/-!
## Refusal lemmas — the strict rules, one per reason
-/

/-- Mid-request-body connections never migrate. -/
theorem not_eligible_of_bodyStream {c : ConnView}
    (h : c.bodyStream = true) : ¬ c.Eligible := by
  intro he
  have hb := he.1
  simp [ConnView.busy, h] at hb

/-- Mid-chunked-body connections never migrate. -/
theorem not_eligible_of_chunkedBodyStream {c : ConnView}
    (h : c.chunkedBodyStream = true) : ¬ c.Eligible := by
  intro he
  have hb := he.1
  simp [ConnView.busy, h] at hb

/-- Connections forwarding a proxied body never migrate. -/
theorem not_eligible_of_proxyBodyForward {c : ConnView}
    (h : c.proxyBodyForward = true) : ¬ c.Eligible := by
  intro he
  have hb := he.1
  simp [ConnView.busy, h] at hb

/-- Connections with an active upstream request never migrate (extracting
them as "idle" would strand the upstream response). -/
theorem not_eligible_of_upstreamGuard {c : ConnView}
    (h : c.upstreamGuard = true) : ¬ c.Eligible := by
  intro he
  have hb := he.1
  simp [ConnView.busy, h] at hb

/-- Connections streaming a response never migrate. -/
theorem not_eligible_of_streamingResponse {c : ConnView}
    (h : c.streamingResponse = true) : ¬ c.Eligible := by
  intro he
  have hb := he.1
  simp [ConnView.busy, h] at hb

/-- **Send-blocked connections never migrate**: pending outbound data is
an in-flight attachment. (This is the seam with the send-path machine —
its blocked set is this field.) -/
theorem not_eligible_of_sendPending {c : ConnView}
    (h : c.sendPending = true) : ¬ c.Eligible := by
  intro he
  have hb := he.1
  simp [ConnView.busy, h] at hb

/-- Forward-proxy connections never migrate. -/
theorem not_eligible_of_forwardProxy {c : ConnView}
    (h : c.forwardProxy = true) : ¬ c.Eligible := by
  intro he
  have hb := he.1
  simp [ConnView.busy, h] at hb

/-- Intercepting-proxy sessions never migrate. -/
theorem not_eligible_of_mitm {c : ConnView}
    (h : c.mitm = true) : ¬ c.Eligible := by
  intro he
  have hb := he.1
  simp [ConnView.busy, h] at hb

/-- Nothing outside the four named protocol classes migrates: handshakes,
WebSockets, tunnels, relays are all refused at the protocol test. -/
theorem not_eligible_of_other {c : ConnView}
    (h : c.protocol = .other) : ¬ c.Eligible := by
  intro he
  have hi := he.2
  rw [h] at hi
  exact hi

/-- An H1 connection with buffered bytes is mid-request: refused. -/
theorem not_eligible_of_h1_buffered {c : ConnView} {n : Nat}
    (h : c.protocol = .plainH1 n) (hn : n ≠ 0) : ¬ c.Eligible := by
  intro he
  have hi := he.2
  rw [h] at hi
  exact hn hi

/-- An H2 connection with active streams is mid-work: refused. -/
theorem not_eligible_of_h2_active {c : ConnView} {a p : Nat}
    (h : c.protocol = .tlsH2 a p) (ha : a ≠ 0) : ¬ c.Eligible := by
  intro he
  have hi := he.2
  rw [h] at hi
  exact ha hi.1

/-!
## The snapshot schema and its round-trip
-/

/-- The protocol class of a snapshot: exactly the four migratable classes,
with the counters *erased* — eligibility pinned them all to zero, so the
schema carries no counter fields at all. -/
inductive SnapProto where
  | h1Plain
  | h1Tls
  | h2Tls
  | h2Plain
  deriving Repr, DecidableEq, Inhabited

/-- The serialized connection: its protocol class plus the opaque session
payload `σ` (keys, sequence numbers, negotiated parameters — whatever the
encryption layer round-trips; its structure is not this model's business). -/
structure Snapshot (σ : Type u) where
  proto : SnapProto
  session : σ
  deriving Repr, DecidableEq, Inhabited

/-- Extraction: refuse ineligible connections; otherwise serialize the
protocol class and attach the session payload. -/
def ConnView.extract (c : ConnView) (session : σ) : Option (Snapshot σ) :=
  if c.Eligible then
    match c.protocol with
    | .plainH1 _ => some ⟨.h1Plain, session⟩
    | .tlsH1 _ => some ⟨.h1Tls, session⟩
    | .tlsH2 _ _ => some ⟨.h2Tls, session⟩
    | .plainH2 _ _ => some ⟨.h2Plain, session⟩
    | .other => none
  else none

/-- The idle connection view a snapshot reconstructs to. -/
def SnapProto.toView : SnapProto → ConnView
  | .h1Plain => ⟨.plainH1 0, false, false, false, false, false, false,
                 false, false, false, false, false⟩
  | .h1Tls => ⟨.tlsH1 0, false, false, false, false, false, false,
               false, false, false, false, false⟩
  | .h2Tls => ⟨.tlsH2 0 0, false, false, false, false, false, false,
               false, false, false, false, false⟩
  | .h2Plain => ⟨.plainH2 0 0, false, false, false, false, false, false,
                 false, false, false, false, false⟩

/-- Injection (adoption): reconstruct the connection view and hand back
the session payload for re-installation. -/
def Snapshot.inject (m : Snapshot σ) : ConnView × σ :=
  (m.proto.toView, m.session)

/-- Extraction refuses exactly the ineligible. -/
theorem ConnView.extract_refuses_ineligible (c : ConnView) (x : σ)
    (h : ¬ c.Eligible) : c.extract x = none := by
  simp [extract, h]

/-- Extraction succeeds on every eligible connection. -/
theorem ConnView.extract_eligible (c : ConnView) (x : σ)
    (h : c.Eligible) : ∃ m, c.extract x = some m := by
  cases hp : c.protocol with
  | other => exact absurd h (not_eligible_of_other hp)
  | plainH1 n => exact ⟨⟨.h1Plain, x⟩, by simp [extract, h, hp]⟩
  | tlsH1 n => exact ⟨⟨.h1Tls, x⟩, by simp [extract, h, hp]⟩
  | tlsH2 a p => exact ⟨⟨.h2Tls, x⟩, by simp [extract, h, hp]⟩
  | plainH2 a p => exact ⟨⟨.h2Plain, x⟩, by simp [extract, h, hp]⟩

/-- **The round-trip, forward**: on eligible states, adoption after
extraction reproduces the connection *exactly* — including the session
payload, bit for bit (`inject ∘ extract = id`). Eligibility is what makes
the erased counters recoverable: they were all zero. -/
theorem ConnView.inject_extract (c : ConnView) (x : σ) (m : Snapshot σ)
    (h : c.Eligible) (hx : c.extract x = some m) : m.inject = (c, x) := by
  obtain ⟨hbusy, hidle⟩ := h
  obtain ⟨proto, bs, cbs, pbf, ug, urs, ursend, sr, sp, sse, fp, mi⟩ := c
  simp only [ConnView.busy] at hbusy
  simp only [Bool.or_eq_false_iff] at hbusy
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ :=
    hbusy
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  cases proto with
  | other => exact hidle.elim
  | plainH1 n =>
    have hn : n = 0 := hidle
    subst hn
    have hel : ConnView.Eligible
        ⟨.plainH1 0, false, false, false, false, false, false,
         false, false, false, false, false⟩ := by decide
    simp only [extract, if_pos hel] at hx
    cases hx
    rfl
  | tlsH1 n =>
    have hn : n = 0 := hidle
    subst hn
    have hel : ConnView.Eligible
        ⟨.tlsH1 0, false, false, false, false, false, false,
         false, false, false, false, false⟩ := by decide
    simp only [extract, if_pos hel] at hx
    cases hx
    rfl
  | tlsH2 a p =>
    obtain ⟨ha, hp⟩ := hidle
    subst ha hp
    have hel : ConnView.Eligible
        ⟨.tlsH2 0 0, false, false, false, false, false, false,
         false, false, false, false, false⟩ := by decide
    simp only [extract, if_pos hel] at hx
    cases hx
    rfl
  | plainH2 a p =>
    obtain ⟨ha, hp⟩ := hidle
    subst ha hp
    have hel : ConnView.Eligible
        ⟨.plainH2 0 0, false, false, false, false, false, false,
         false, false, false, false, false⟩ := by decide
    simp only [extract, if_pos hel] at hx
    cases hx
    rfl

/-- Adoption lands eligible: the reconstructed view can immediately serve
traffic — and could itself migrate again. -/
theorem SnapProto.toView_eligible (p : SnapProto) :
    p.toView.Eligible := by
  cases p <;> decide

/-- **The round-trip, backward**: extracting a freshly adopted connection
reproduces the snapshot exactly (`extract ∘ inject = id`). The schema is
precisely the information content of an eligible connection — no more, no
less. -/
theorem Snapshot.extract_inject (m : Snapshot σ) :
    m.inject.1.extract m.inject.2 = some m := by
  obtain ⟨p, x⟩ := m
  cases p <;> rfl

end Flow
