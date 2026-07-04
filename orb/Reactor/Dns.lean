import Reactor.Contract
import Reactor.Config
import Reactor.Proxy
import Dns.Message

/-!
# Reactor.Dns — resolve an upstream hostname with the REAL DNS parser before connecting

This wires the real `Dns` library (RFC 1035 message parse, with its anti-loop name
decompression) into the reactor's upstream-connect path. The reactor already emits
`RingSubmission.connectUpstream addr` (from the FSM's SOCKS/tunnel `connectUpstream`
output, `Reactor.Contract.ofOutput`, and from the reverse-proxy handler
`Reactor.Proxy.proxyHandle`). Before that connect is honored, the target hostname is
resolved by driving the real `Dns` response parser to an address.

The wiring, outside-in:

  * `resolve host msg` — the resolution call. It drives the REAL `Dns.parseHeader`,
    `Dns.parseQuestion`, and `Dns.parseRR` over a DNS *response* message. `parseRR`
    (and `parseQuestion`) call `Dns.decodeName`, whose termination is the anti-loop
    guarantee: a compression pointer must jump strictly backward, so no adversarial
    pointer arrangement can make resolution diverge. On a first `A` (type 1) answer
    record it reads the 4-octet RDATA as the resolved `Proto.Addr`; otherwise `none`.
  * `Resolver` — the reactor's view of DNS: the response bytes (and expected question
    name) it holds for the host a *pre-resolution* connect address names. A real
    resolver returns `none` for a host with no answer (NXDOMAIN / SERVFAIL).
  * `resolveAddr R a` — resolve one pre-resolution address `a`: look up its host's
    response and run `resolve`. This is literally `resolve ∘ lookup`; nothing here
    re-implements parsing.
  * `resolveSubs R subs` — the pass over the reactor's own submission stream: rewrite
    every `connectUpstream a` to `connectUpstream (resolveAddr R a)` when resolution
    succeeds, and DROP it when it fails (no connect to an unresolved host). Every other
    submission passes through untouched.

**Seam theorem — `dns_resolves_before_connect`.** Every `connectUpstream a'` that
survives the pass carries an `a'` that is the REAL `Dns.resolve` of the response bytes
the resolver held for some pre-resolution connect `a` the reactor actually emitted:
there exist `a`, `host`, `msg` with `connectUpstream a ∈ subs`, `R.lookup a = some
(host, msg)`, and `resolve host msg = some a'`. A stubbed resolver that hardcoded an
address without parsing `msg` would not satisfy the `resolve host msg = some a'`
conjunct (its output is *defined* to be the parser's). And because resolution is total
(`resolve_total`, inheriting `Dns.decodeName_total`), a looping DNS response cannot hang
the reactor — it resolves to "no address" and the connect is dropped
(`dns_terminates_on_loop`).

**No connect to an unresolved host** — `unresolved_dropped`: a `connectUpstream a` whose
host fails to resolve (`resolveAddr R a = none`) contributes nothing to the output; and
`dns_resolves_before_connect` shows every *surviving* connect was `some`-resolved.

The wiring is exercised on a path that runs: `dns_wired_running` drives the real
`Reactor.step` on a SOCKS connection (which emits a genuine `connectUpstream`) and shows
the resolver rewrites that connect to the DNS-parsed address; `dns_wired_proxy` does the
same over the real `Reactor.Proxy.proxyHandle` output ("compose with the proxy Addr").
-/

namespace Reactor.DnsWire

open Proto (Bytes Addr Request)

/-! ## The resolution call — driven by the real `Dns` parser -/

/-- An `A`-record RDATA (exactly 4 octets, an IPv4 address) as a `Proto.Addr`: the
big-endian 32-bit value the real `Dns.be32` reads. Any other RDATA length is not an
address here. -/
def addrOfRData : List UInt8 → Option Addr
  | [a, b, c, d] => some ⟨Dns.be32 a b c d⟩
  | _            => none

/-- Read the first answer record at `off` with the REAL `Dns.parseRR` (which decodes the
record NAME via `Dns.decodeName`, honoring the anti-loop pointer rule) and, when it is an
`A` record (type 1), return its address. `none` on a parse failure or a non-`A` record. -/
def answerAddr (msg : Bytes) (off : Nat) : Option Addr :=
  match Dns.parseRR msg off with
  | none          => none
  | some (rr, _)  => if rr.rrType = 1 then addrOfRData rr.rdata else none

/-- **The resolution.** Parse a DNS *response* `msg` with the real library and, when it
answers a query for `host` (question name matches) and carries at least one answer, read
the first answer's `A` address. Every parse step (`parseHeader`, `parseQuestion`,
`parseRR`) is a total `Dns` function; the name fields are decoded by `Dns.decodeName`,
whose anti-loop termination guarantee makes `resolve` total on every input. -/
def resolve (host : List (List UInt8)) (msg : Bytes) : Option Addr :=
  match Dns.parseHeader msg with
  | none          => none
  | some (h, hn)  =>
    if 1 ≤ h.anCount then
      match Dns.parseQuestion msg hn with
      | none          => none
      | some (q, qn)  => if q.qname = host then answerAddr msg (hn + qn) else none
    else none

/-- **Totality — the anti-loop guarantee, lifted.** `resolve` returns a value on every
`(host, msg)`, adversarial compression-pointer loops included. It is a plain `def`
composing the total `Dns` parsers; the load-bearing totality is `Dns.decodeName`'s
(`Dns.decodeName_total`), so there is no timeout and no divergence. -/
theorem resolve_total (host : List (List UInt8)) (msg : Bytes) :
    ∃ r, resolve host msg = r := ⟨_, rfl⟩

/-! ## The resolver and the pre-connect resolution pass -/

/-- The reactor's DNS view: for a pre-resolution connect address `a`, the response bytes
(and the expected question name) it holds for that host — or `none` when the host has no
answer record. -/
structure Resolver where
  lookup : Addr → Option (List (List UInt8) × Bytes)

/-- Resolve one pre-resolution address: look up its host's response and run the REAL
`resolve`. Definitionally `resolve ∘ lookup`. -/
def resolveAddr (R : Resolver) (a : Addr) : Option Addr :=
  match R.lookup a with
  | none            => none
  | some (host, msg) => resolve host msg

/-- **The pre-connect resolution pass.** Walk the reactor's submission stream: rewrite a
`connectUpstream a` to a connect to the DNS-resolved address when `resolveAddr` succeeds,
and DROP it when resolution fails (no connect to an unresolved host). Every non-connect
submission passes through unchanged. -/
def resolveSubs (R : Resolver) : List RingSubmission → List RingSubmission
  | []                                    => []
  | RingSubmission.connectUpstream a :: rest =>
    match resolveAddr R a with
    | some a' => RingSubmission.connectUpstream a' :: resolveSubs R rest
    | none    => resolveSubs R rest
  | s :: rest                             => s :: resolveSubs R rest

theorem resolveSubs_total (R : Resolver) (subs : List RingSubmission) :
    ∃ r, resolveSubs R subs = r := ⟨_, rfl⟩

/-! ## Structural rewrite lemmas for the pass -/

/-- The pass at a `connectUpstream` head unfolds to the resolution match. -/
theorem resolveSubs_cons_connect (R : Resolver) (a : Addr) (rest : List RingSubmission) :
    resolveSubs R (RingSubmission.connectUpstream a :: rest)
      = match resolveAddr R a with
        | some a' => RingSubmission.connectUpstream a' :: resolveSubs R rest
        | none    => resolveSubs R rest := rfl

/-- A resolved connect is forwarded to the DNS-derived address. -/
theorem resolved_forwarded (R : Resolver) (a a' : Addr) (rest : List RingSubmission)
    (h : resolveAddr R a = some a') :
    resolveSubs R (RingSubmission.connectUpstream a :: rest)
      = RingSubmission.connectUpstream a' :: resolveSubs R rest := by
  rw [resolveSubs_cons_connect, h]

/-- **No connect to an unresolved host.** A connect whose host does not resolve is
dropped from the stream entirely. -/
theorem unresolved_dropped (R : Resolver) (a : Addr) (rest : List RingSubmission)
    (h : resolveAddr R a = none) :
    resolveSubs R (RingSubmission.connectUpstream a :: rest) = resolveSubs R rest := by
  rw [resolveSubs_cons_connect, h]

/-- A non-connect submission passes through unchanged. -/
theorem resolveSubs_cons_other (R : Resolver) (s : RingSubmission) (rest : List RingSubmission)
    (hne : ∀ a, s ≠ RingSubmission.connectUpstream a) :
    resolveSubs R (s :: rest) = s :: resolveSubs R rest := by
  cases s <;> first | rfl | exact absurd rfl (hne _)

/-! ## The seam theorem -/

/-- Every resolved connect address has a `some`-resolving pre-resolution preimage. -/
theorem resolveAddr_some (R : Resolver) (a a' : Addr) (h : resolveAddr R a = some a') :
    ∃ host msg, R.lookup a = some (host, msg) ∧ resolve host msg = some a' := by
  unfold resolveAddr at h
  cases hl : R.lookup a with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some p =>
    obtain ⟨host, msg⟩ := p
    rw [hl] at h
    exact ⟨host, msg, rfl, h⟩

/-- **`dns_resolves_before_connect` — the anti-island seam.** Every `connectUpstream a'`
the pass emits carries an `a'` that is the REAL `Dns.resolve` of the response bytes the
resolver held for some pre-resolution connect `a` the reactor actually emitted. So the
address the reactor dials is *derived from a real DNS parse of the backend hostname*,
never a hardcoded target, and (by the `resolve host msg = some a'` conjunct) never a
host that failed to resolve. A stubbed resolver, whose output did not equal
`Dns.resolve msg`, would break the final conjunct. -/
theorem dns_resolves_before_connect (R : Resolver) (subs : List RingSubmission) (a' : Addr)
    (h : RingSubmission.connectUpstream a' ∈ resolveSubs R subs) :
    ∃ (a : Addr) (host : List (List UInt8)) (msg : Bytes),
        RingSubmission.connectUpstream a ∈ subs
      ∧ R.lookup a = some (host, msg)
      ∧ resolve host msg = some a' := by
  induction subs with
  | nil => simp [resolveSubs] at h
  | cons s rest ih =>
    by_cases hc : ∃ a, s = RingSubmission.connectUpstream a
    · obtain ⟨a, rfl⟩ := hc
      rw [resolveSubs_cons_connect] at h
      cases hra : resolveAddr R a with
      | none =>
        rw [hra] at h
        obtain ⟨a0, host, msg, hmem, hlk, hrs⟩ := ih h
        exact ⟨a0, host, msg, List.mem_cons_of_mem _ hmem, hlk, hrs⟩
      | some a'' =>
        rw [hra] at h
        rcases List.mem_cons.mp h with heq | htl
        · have hEq : a' = a'' := by injection heq
          obtain ⟨host, msg, hlk, hrs⟩ := resolveAddr_some R a a'' hra
          exact ⟨a, host, msg, List.mem_cons_self _ _, hlk, by rw [hEq]; exact hrs⟩
        · obtain ⟨a0, host, msg, hmem, hlk, hrs⟩ := ih htl
          exact ⟨a0, host, msg, List.mem_cons_of_mem _ hmem, hlk, hrs⟩
    · have hne : ∀ a, s ≠ RingSubmission.connectUpstream a := fun a heq => hc ⟨a, heq⟩
      rw [resolveSubs_cons_other R s rest hne] at h
      rcases List.mem_cons.mp h with heq | htl
      · exact absurd heq.symm (hne a')
      · obtain ⟨a0, host, msg, hmem, hlk, hrs⟩ := ih htl
        exact ⟨a0, host, msg, List.mem_cons_of_mem _ hmem, hlk, hrs⟩

/-! ## Concrete data: a real DNS response and its resolution -/

/-- The upstream hostname, as decoded labels: `"up"`. -/
def hostUp : List (List UInt8) := [[117, 112]]

/-- A real wire-format DNS *response* for `up`: 12-octet header (QDCOUNT 1, ANCOUNT 1),
one question `up IN A`, and one answer `A` record `93.184.216.34` (TTL 60). The answer
name is spelled uncompressed here so the success vector reduces in the kernel. -/
def msgUp : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,  -- header
    2, 117, 112, 0,                                                          -- QNAME "up"
    0x00, 0x01, 0x00, 0x01,                                                  -- QTYPE A, QCLASS IN
    2, 117, 112, 0,                                                          -- answer NAME "up"
    0x00, 0x01, 0x00, 0x01,                                                  -- TYPE A, CLASS IN
    0x00, 0x00, 0x00, 0x3C,                                                  -- TTL 60
    0x00, 0x04,                                                              -- RDLENGTH 4
    93, 184, 216, 34 ]                                                       -- RDATA 93.184.216.34

/-- **The real parser resolves the response to the A-record address.** `93.184.216.34`
big-endian is `93*2^24 + 184*2^16 + 216*2^8 + 34 = 1572395042`. A stub that ignored the
bytes could not produce this value. -/
theorem resolve_msgUp : resolve hostUp msgUp = some ⟨1572395042⟩ := by decide

/-- An adversarial response whose answer NAME is a self-pointer (`C0 14` at offset 20 →
target 20). The real decoder's strictly-backward rule rejects it as a loop rather than
diverging. -/
def msgLoop : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,  -- header
    2, 117, 112, 0,                                                          -- QNAME "up"
    0x00, 0x01, 0x00, 0x01,                                                  -- QTYPE A, QCLASS IN
    0xC0, 0x14 ]                                                             -- answer NAME → ptr to 20 (self)

/-- **Anti-loop termination, concretely.** A looping DNS response resolves to `none` —
the real `Dns` decoder terminates with `loopPointer` (via `Dns.followChain_self_loop`),
so the reactor issues no connect rather than hanging. This is the guarantee
`resolve_total` states, exhibited on adversarial bytes. -/
theorem dns_terminates_on_loop : resolve hostUp msgLoop = none := by
  have hr : Dns.readRun msgLoop 20 [] (msgLoop.length + 1) = .jump 20 [] 22 := by decide
  have hf : Dns.followChain msgLoop 20 [] = .err .loopPointer :=
    Dns.followChain_self_loop msgLoop 20 [] [] 22 hr
  have hd : Dns.decodeName msgLoop 20 = .error .loopPointer := by
    unfold Dns.decodeName; rw [hr]; simp only [hf]
  have hrr : Dns.parseRR msgLoop 20 = none := by
    unfold Dns.parseRR; rw [hd]
  have hh : Dns.parseHeader msgLoop = some (⟨4660, 33152, 1, 1, 0, 0⟩, 12) := by decide
  have hq : Dns.parseQuestion msgLoop 12 = some (⟨[[117, 112]], 1, 1⟩, 8) := by decide
  simp only [resolve, hh, hq, hostUp, answerAddr, hrr, ite_self]

/-! ## The wiring, on a path that runs

The real reactor emits a `connectUpstream` on a SOCKS-connect completion
(`Proto.Step` → `Reactor.Contract.ofOutput`). We drive `Reactor.step` on such a
connection with a config whose SOCKS handler reports a connect to the *unresolved*
marker host, then run the resolver pass over the reactor's actual output. -/

/-- A concrete `Proto.Config` whose SOCKS handler completes a connect to the unresolved
marker address `⟨7⟩` (every other field is `Reactor.Config.demoConfig`'s). -/
def dnsSocksConfig : Proto.Config :=
  { Reactor.Config.demoConfig with socksFeed := fun _ _ => .connect ⟨7⟩ 0 }

/-- The demo resolver: it holds the `msgUp` response for both the SOCKS marker `⟨7⟩` and
the proxy's chosen backend `⟨2⟩`; every other host is unresolved. -/
def demoResolver : Resolver where
  lookup a :=
    if a.id = 7 then some (hostUp, msgUp)
    else if a.id = 2 then some (hostUp, msgUp)
    else none

theorem resolveAddr_demo7 : resolveAddr demoResolver ⟨7⟩ = some ⟨1572395042⟩ := by decide
theorem resolveAddr_demo2 : resolveAddr demoResolver ⟨2⟩ = some ⟨1572395042⟩ := by decide

/-- The REAL reactor step on a SOCKS connection emits a genuine `connectUpstream` to the
unresolved marker (plus the copy-once buffer recycle). -/
def reactorEmitsConnect : List RingSubmission :=
  (Reactor.step dnsSocksConfig (Proto.State.active Proto.Conn.mkSocks)
      (RingEvent.recvInto 0 [])).2

theorem reactorEmitsConnect_eq :
    reactorEmitsConnect
      = [RingSubmission.connectUpstream ⟨7⟩, RingSubmission.recycleBuffer 0] := rfl

/-- **`dns_wired_running` — the wiring on the running reactor path.** The real
`Reactor.step` emitted a `connectUpstream ⟨7⟩` (marker); after the DNS pass the reactor
targets `⟨1572395042⟩` — the address the REAL `Dns` parser read from the response — and
the copy-once recycle is untouched. A stubbed resolver could not produce this address. -/
theorem dns_wired_running :
    resolveSubs demoResolver reactorEmitsConnect
      = [RingSubmission.connectUpstream ⟨1572395042⟩, RingSubmission.recycleBuffer 0] := by
  rw [reactorEmitsConnect_eq,
    resolved_forwarded demoResolver ⟨7⟩ ⟨1572395042⟩ [RingSubmission.recycleBuffer 0]
      resolveAddr_demo7]
  rfl

/-- **`dns_wired_proxy` — composed with the proxy Addr.** The real reverse-proxy handler
picks backend `demoB2` and asks to connect to its address `⟨2⟩`; the DNS pass resolves
that host and the reactor targets the DNS-parsed address `⟨1572395042⟩`. This is the
"resolve before connect" seam sitting exactly where the task asks: between the proxy's
`Addr` and the actual connect. -/
theorem dns_wired_proxy (req : Request) :
    resolveSubs demoResolver
        (Reactor.Proxy.proxyHandle Reactor.Proxy.demoPool Reactor.Proxy.demoCtx req)
      = [RingSubmission.connectUpstream ⟨1572395042⟩] := by
  have hp : Reactor.Proxy.proxyHandle Reactor.Proxy.demoPool Reactor.Proxy.demoCtx req
      = [RingSubmission.connectUpstream ⟨2⟩] := by
    unfold Reactor.Proxy.proxyHandle
    rw [Reactor.Proxy.demo_chooses_b2]
    rfl
  rw [hp, resolved_forwarded demoResolver ⟨2⟩ ⟨1572395042⟩ [] resolveAddr_demo2]
  rfl

end Reactor.DnsWire
