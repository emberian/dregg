/-!
# HTTP forward proxy: absolute-URI requests, interception rules, CONNECT tunnels

A *forward proxy* is an intermediary the client explicitly addresses: instead of
opening a connection to the origin server, the client sends the whole request to
the proxy and asks it to fetch (or tunnel to) the target on its behalf. This
file models the three surfaces of such a proxy as total functions with real
theorems.

## RFC sections captured

* **RFC 9112 §3.2.2 (absolute-form).** For an ordinary proxied request the
  client sends the target URI in absolute-form (`GET http://host/p HTTP/1.1`).
  "When a proxy receives a request with an absolute-form of request-target, the
  proxy MUST ignore the received Host header field (if any) and instead replace
  it with the host information of the request-target." Modeled by `normalize`:
  the effective authority is taken from the request-target, and the stale Host
  header value is provably irrelevant (`absolute_form_host_override`,
  `host_header_irrelevant`).

* **RFC 9110 §9.3.6 (CONNECT).** "The CONNECT method requests that the recipient
  establish a tunnel to the destination origin server ... and, if successful,
  thereafter restrict its behavior to blind forwarding of data, in both
  directions, until the tunnel is closed." "Any 2xx response indicates that the
  sender will switch to tunnel mode ...; any response other than a successful
  response indicates that the tunnel has not yet been formed." Modeled by
  `tstep`: the recipient reaches `connected` only from `connecting` on an
  `upstreamOk` event (the upstream connect succeeding), and application bytes are
  blindly relayed *only* in `connected`, in both directions.

* **Interception surface.** An ordered rule list; each rule matches on
  host / path / port / protocol / method and carries an action
  (`allow` / `block` / `record` / `modify`). The first matching rule decides;
  `block` produces a custom local response and never reaches upstream; `modify`
  applies header operations before forwarding. (This is the configurable
  policy surface RFC 9110 §9.3.6 recommends: "Proxies that support CONNECT
  SHOULD restrict its use to ... a configurable list of safe request targets.")

## Key theorems

* `connect_no_relay_before_connected` — no client↔upstream bytes escape before
  the tunnel is established, in either direction.
* `enter_connected_requires_upstreamOk`, `run_connected_needs_upstreamOk` —
  `connected` is reachable only after the upstream connect succeeds.
* `proxy_rule_first_match` — the first matching rule decides; later rules are
  ignored (`proxy_later_rules_ignored`).
* `block_no_upstream` / `block_yields_custom_response` — a blocked request never
  reaches upstream and returns exactly the configured response.

## Boundaries / UNCLOSED

* The upstream connect itself (DNS, TCP handshake, TLS) is a boundary: it is
  represented by the opaque event `upstreamOk` / `upstreamErr`. We prove the
  tunnel state machine's behavior *relative to* that event, not the transport.
* Byte relay is modeled as the identity on payloads; congestion, framing, and
  connection teardown ordering ("send outstanding data, then close both sides")
  are not modeled here.
* Request/response *parsing* is out of scope; requests enter as structured
  values (as in the sibling `Socks` and `Ws` libraries).
-/

namespace ForwardProxy

def version : String := "0.1.0"

/-- Raw byte strings, modeled as lists (matching the other libraries here). -/
abbrev Bytes := List UInt8

/-! ## Requests, responses, header operations -/

/-- Request method. `connect` is singled out because it selects the tunnel
path; `other` carries any extension token. -/
inductive Method where
  | get | post | put | delete | connect | other (name : String)
deriving DecidableEq, Repr

/-- Header field list: ordered name/value pairs. -/
abbrev Headers := List (String × String)

/-- A structured proxied request. `scheme`/`host`/`port`/`path` come from the
absolute-form request-target; `headers` is the forwarded field section. -/
structure Request where
  method  : Method
  scheme  : String
  host    : String
  port    : Nat
  path    : List String
  headers : Headers
deriving Repr

/-- A response the proxy can synthesize locally (e.g. for a blocked request). -/
structure Response where
  status  : Nat
  headers : Headers
  body    : Bytes
deriving Repr

/-- A header operation applied by a `modify` action. `set` replaces any existing
occurrences of the key with a single new pair; `remove` drops all of them. -/
inductive HeaderOp where
  | set (key value : String)
  | remove (key : String)
deriving Repr

/-- Apply one header operation. -/
def applyOp : HeaderOp → Headers → Headers
  | .set k v, hs => (k, v) :: hs.filter (fun kv => kv.1 != k)
  | .remove k, hs => hs.filter (fun kv => kv.1 != k)

/-- Apply a sequence of header operations left to right. -/
def applyOps (ops : List HeaderOp) (hs : Headers) : Headers :=
  ops.foldl (fun acc op => applyOp op acc) hs

/-- **`remove` erases the key.** After `applyOp (.remove k)`, no field with name
`k` survives. -/
theorem remove_absent (k : String) (hs : Headers) :
    ∀ kv ∈ applyOp (.remove k) hs, kv.1 ≠ k := by
  intro kv hmem
  simp only [applyOp, List.mem_filter] at hmem
  have hne : (kv.1 != k) = true := hmem.2
  exact ne_of_apply_ne (fun s => (s == k)) (by simpa [bne] using hne)

/-- **`set` installs the value at the head.** After `applyOp (.set k v)`, the
first field is exactly `(k, v)`. -/
theorem set_head (k v : String) (hs : Headers) :
    (applyOp (.set k v) hs).head? = some (k, v) := by
  simp [applyOp]

/-! ## Absolute-form request handling (RFC 9112 §3.2.2) -/

/-- A request as it arrived on the wire in absolute-form: the request-target
carries the authority (`targetHost` / `targetPort`), and there may also be a
(possibly stale) `Host` header value that the proxy MUST ignore. -/
structure WireReq where
  method     : Method
  scheme     : String
  targetHost : String
  targetPort : Nat
  path       : List String
  hostHeader : String
  extra      : Headers
deriving Repr

/-- Normalize a wire request: take the authority from the request-target and
regenerate the `Host` field from it, discarding the received `Host` value
(RFC 9112 §3.2.2). -/
def normalize (w : WireReq) : Request :=
  { method := w.method, scheme := w.scheme,
    host := w.targetHost, port := w.targetPort, path := w.path,
    headers := ("Host", w.targetHost) :: w.extra }

/-- **Absolute-form authority wins.** The effective host of a normalized request
is the request-target host, never the received `Host` header. -/
theorem absolute_form_host_override (w : WireReq) :
    (normalize w).host = w.targetHost := rfl

/-- **The received `Host` header is irrelevant.** Two wire requests that differ
only in their `Host` header value normalize identically. -/
theorem host_header_irrelevant (w : WireReq) (h₁ h₂ : String) :
    normalize { w with hostHeader := h₁ } = normalize { w with hostHeader := h₂ } :=
  rfl

/-! ## Ordered interception rules -/

/-- A match criterion: each present field must match the request; an absent
field (`none`) is a wildcard. `path` is matched as a segment prefix. -/
structure Criteria where
  host   : Option String
  path   : Option (List String)
  port   : Option Nat
  proto  : Option String
  method : Option Method
deriving Repr

/-- The action a matched rule dictates. -/
inductive Action where
  | allow
  | block (resp : Response)
  | record
  | modify (ops : List HeaderOp)
deriving Repr

/-- A single interception rule. -/
structure Rule where
  crit   : Criteria
  action : Action
deriving Repr

/-- Optional-field match: wildcard when absent, exact equality when present. -/
def optMatch {α} [DecidableEq α] (o : Option α) (v : α) : Bool :=
  match o with
  | none => true
  | some x => decide (x = v)

/-- Does a request satisfy a criterion? Conjunction over the present fields;
`path` uses a segment-prefix test. -/
def matchesCriteria (c : Criteria) (r : Request) : Bool :=
  optMatch c.host r.host
    && (match c.path with | none => true | some p => p.isPrefixOf r.path)
    && optMatch c.port r.port
    && optMatch c.proto r.scheme
    && optMatch c.method r.method

/-- The action selected for a request: the action of the first matching rule, or
`none` when no rule matches (the proxy's default is to forward untouched). -/
def chosenAction (rules : List Rule) (r : Request) : Option Action :=
  (rules.find? (fun rule => matchesCriteria rule.crit r)).map (·.action)

/-- The disposition of a request after interception. -/
inductive Disposition where
  | forward (r : Request)
  | respondLocal (resp : Response)
deriving Repr

/-- Turn a chosen action into a disposition. `block` responds locally; every
other action forwards (possibly after header rewriting). -/
def applyAction (r : Request) : Action → Disposition
  | .allow => .forward r
  | .record => .forward r
  | .modify ops => .forward { r with headers := applyOps ops r.headers }
  | .block resp => .respondLocal resp

/-- Full interception step: choose the action, then dispose. With no matching
rule the request is forwarded unchanged. -/
def dispatch (rules : List Rule) (r : Request) : Disposition :=
  match chosenAction rules r with
  | none => .forward r
  | some a => applyAction r a

/-- Does a disposition send the request upstream? -/
def reachesUpstream : Disposition → Bool
  | .forward _ => true
  | .respondLocal _ => false

/-! ### First-match list lemma -/

/-- `find?` returns the first element satisfying the predicate: if every element
before `x` fails and `x` succeeds, the result is `x`. -/
theorem find?_first {α} {p : α → Bool} {pre : List α} {x : α} {post : List α}
    (hpre : ∀ q ∈ pre, p q = false) (hx : p x = true) :
    (pre ++ x :: post).find? p = some x := by
  induction pre with
  | nil => simp [List.find?, hx]
  | cons a as ih =>
    have ha : p a = false := hpre a (List.mem_cons_self _ _)
    simp only [List.cons_append, List.find?, ha]
    exact ih (fun q hq => hpre q (List.mem_cons_of_mem _ hq))

/-! ### First-match theorems -/

/-- **The first matching rule decides.** If the rule table splits as
`pre ++ r :: post` where no rule in `pre` matches and `r` matches, the chosen
action is exactly `r.action` — later rules never enter into it. -/
theorem proxy_rule_first_match {rules : List Rule} {r : Rule} {req : Request}
    {pre post : List Rule} (hsplit : rules = pre ++ r :: post)
    (hpre : ∀ q ∈ pre, matchesCriteria q.crit req = false)
    (hr : matchesCriteria r.crit req = true) :
    chosenAction rules req = some r.action := by
  unfold chosenAction
  rw [hsplit, find?_first hpre hr]
  rfl

/-- **Later rules are ignored.** Once a first match is fixed, replacing the rules
that follow it does not change the decision. -/
theorem proxy_later_rules_ignored {r : Rule} {req : Request}
    {pre post post' : List Rule}
    (hpre : ∀ q ∈ pre, matchesCriteria q.crit req = false)
    (hr : matchesCriteria r.crit req = true) :
    chosenAction (pre ++ r :: post) req = chosenAction (pre ++ r :: post') req := by
  rw [proxy_rule_first_match rfl hpre hr, proxy_rule_first_match rfl hpre hr]

/-- **A blocked request never reaches upstream.** If the chosen action is
`block resp`, the request is answered locally with exactly `resp`. -/
theorem block_yields_custom_response {rules : List Rule} {req : Request}
    {resp : Response} (h : chosenAction rules req = some (.block resp)) :
    dispatch rules req = .respondLocal resp := by
  simp only [dispatch, h, applyAction]

/-- **No upstream on block.** A blocked request's disposition does not go
upstream. -/
theorem block_no_upstream {rules : List Rule} {req : Request} {resp : Response}
    (h : chosenAction rules req = some (.block resp)) :
    reachesUpstream (dispatch rules req) = false := by
  rw [block_yields_custom_response h]; rfl

/-- **`modify` forwards with rewritten headers.** -/
theorem modify_applies_ops {rules : List Rule} {req : Request} {ops : List HeaderOp}
    (h : chosenAction rules req = some (.modify ops)) :
    dispatch rules req = .forward { req with headers := applyOps ops req.headers } := by
  simp only [dispatch, h, applyAction]

/-! ## CONNECT tunnel establishment (RFC 9110 §9.3.6) -/

/-- Tunnel phase at the proxy. `idle` before the request; `connecting` while the
upstream connect is outstanding; `connected` once it succeeded and a 2xx was
returned (blind-forwarding mode); `failed` on upstream failure. -/
inductive TPhase where
  | idle | connecting | connected | failed
deriving DecidableEq, Repr

/-- Tunnel events. `connectReq` is the client's CONNECT; `upstreamOk` /
`upstreamErr` are the (boundary) outcomes of the proxy's connect to the target;
`payload` carries application bytes to relay. -/
inductive TEv where
  | connectReq | upstreamOk | upstreamErr | payload
deriving DecidableEq, Repr

/-- The tunnel step. A CONNECT starts the upstream connect; success moves to
`connected`, failure to `failed`; every other pair stutters (in particular
`connected` and `failed` are absorbing). -/
def tstep : TPhase → TEv → TPhase
  | .idle, .connectReq => .connecting
  | .connecting, .upstreamOk => .connected
  | .connecting, .upstreamErr => .failed
  | p, _ => p

/-- **Determinism.** `tstep` is a function: equal inputs give equal outputs. -/
theorem tstep_deterministic {p₁ p₂ : TPhase} {e₁ e₂ : TEv}
    (hp : p₁ = p₂) (he : e₁ = e₂) : tstep p₁ e₁ = tstep p₂ e₂ := by
  rw [hp, he]

/-- `connected` is absorbing. -/
theorem tstep_connected_absorbing (e : TEv) : tstep .connected e = .connected := by
  cases e <;> rfl

/-- `failed` is absorbing. -/
theorem tstep_failed_absorbing (e : TEv) : tstep .failed e = .failed := by
  cases e <;> rfl

/-- **Establishment requires the upstream connect to succeed.** Entering
`connected` from any other phase is possible only from `connecting` on the
`upstreamOk` event. -/
theorem enter_connected_requires_upstreamOk {p : TPhase} {e : TEv}
    (hpre : p ≠ .connected) (hpost : tstep p e = .connected) :
    p = .connecting ∧ e = .upstreamOk := by
  cases p <;> cases e <;> simp_all [tstep]

/-! ### The relay gate -/

/-- Relay direction (client→upstream or upstream→client); the relay is
identical in both, per "blind forwarding of data, in both directions". -/
inductive Dir where
  | c2s | s2c
deriving DecidableEq, Repr

/-- The relay gate: open exactly in `connected`. -/
def TPhase.up : TPhase → Bool
  | .connected => true
  | _ => false

/-- Application-byte egress across the tunnel, gated by the phase. Closed gate
forwards nothing; open gate is the identity. -/
def egress (p : TPhase) (_dir : Dir) (payload : Bytes) : Bytes :=
  if p.up then payload else []

/-- **No relay before the tunnel is established.** In any phase other than
`connected`, no client↔upstream bytes escape, in either direction. -/
theorem connect_no_relay_before_connected (p : TPhase) (dir : Dir) (payload : Bytes)
    (h : p ≠ .connected) : egress p dir payload = [] := by
  have hup : p.up = false := by cases p <;> simp_all [TPhase.up]
  simp [egress, hup]

/-- **Blind forwarding once established.** After `connected`, the relay is the
identity on the payload, in either direction. -/
theorem connect_relay_transparent (dir : Dir) (payload : Bytes) :
    egress .connected dir payload = payload := rfl

/-- Direction independence of the relay. -/
theorem egress_dir_indep (p : TPhase) (payload : Bytes) :
    egress p Dir.c2s payload = egress p Dir.s2c payload := rfl

/-! ### Trace-level ordering -/

/-- Fold the tunnel state machine over a sequence of events. -/
def run (p : TPhase) (evs : List TEv) : TPhase :=
  evs.foldl tstep p

/-- **The tunnel opens only after an `upstreamOk`.** If a run starting in a
not-yet-connected phase reaches `connected`, the event sequence contained the
successful upstream-connect event. -/
theorem run_connected_needs_upstreamOk (evs : List TEv) (p : TPhase)
    (hp : p ≠ .connected) (h : run p evs = .connected) :
    TEv.upstreamOk ∈ evs := by
  induction evs generalizing p with
  | nil =>
    simp only [run, List.foldl_nil] at h
    exact absurd h hp
  | cons e es ih =>
    simp only [run, List.foldl_cons] at h
    by_cases hc : tstep p e = .connected
    · have := enter_connected_requires_upstreamOk hp hc
      rw [this.2]; exact List.mem_cons_self _ _
    · exact List.mem_cons_of_mem _ (ih (tstep p e) hc h)

end ForwardProxy
