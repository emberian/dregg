# Reactor.Config — the real parser, wired

`Reactor/Config.lean` instantiates `Proto.Config.h1Parse` with the proven-total
arena parser. Before this, `h1Parse` was an abstract `Config` field: every
`Proto.step` theorem held uniformly "for all codecs," but no concrete parser was
ever plugged in, so nothing tied the FSM's dispatch path to the real parsed
bytes. This file supplies that instance and proves the bytes flow through.

## The pieces

- `resolveBytes : Store → Entry → Bytes` — reads one arena view entry back to its
  bytes through the proven-total `Store.resolve`. Bytes, not `String`, so it
  stays off the UTF-8 `Option`. On a `complete` parse the `none` arm is dead
  (`parse_wf` + `resolve_total`); `resolve` is total-as-`Option`, so the match is
  still spelled.
- `protoReqOf : Arena.Parse.Request → Proto.Request` — the single point that
  fills `Request.{method,target,version,headers}`, each field being the resolved
  bytes of the corresponding arena entry. Both the adapter and the theorem
  reference it, so they cannot drift.
- `deriveKeepAlive : List (Bytes × Bytes) → Bool` — default `true` (HTTP/1.1
  persistent); an explicit `Connection: close` (compared against the canonical
  lowercase header name the arena emits) turns it off.
- `arenaToProto : Arena.Parse.Outcome → Proto.ParseOutcome` — the adapter:
  - `complete req` → `ParseOutcome.request req.consumed (protoReqOf req) …`
  - `incomplete`   → `ParseOutcome.incomplete`
  - `error _ _`    → `ParseOutcome.error` (the FSM answers from
    `Config.errorResponse`, the canned 400 below, and closes)
- `h1ParseFn := arenaToProto ∘ Arena.Parse.parse` (default header cap).
- `demoConfig : Proto.Config` — wires `h1Parse := h1ParseFn`, caps
  (`maxHeaderBytes 65536`, `maxPrefixBytes 4096`), and canned 400 / 431
  responses. The non-HTTP/1.1 codec fields (TLS, HTTP/2, WebSocket, SOCKS,
  PROXY-prefix) are placeholder totals — inert/refusing behavior, out of scope
  for this wiring, which is the plaintext HTTP/1.1 lane the arena parser drives.

## The theorem the audit demanded

`h1Parse_complete_content`: when `Arena.Parse.parse buf = complete req`,

    h1ParseFn buf = .request req.consumed (protoReqOf req) (deriveKeepAlive …)
      ∧ (protoReqOf req).method  = resolveBytes req.store req.method
      ∧ (protoReqOf req).target  = resolveBytes req.store req.target
      ∧ (protoReqOf req).version = resolveBytes req.store req.version

i.e. the resulting `Request`'s method/target/version are *exactly* the arena
entries resolved through `Store.resolve` — nothing discarded, nothing invented.
A degenerate adapter returning an empty `Request` (a "bare id") would fail the
three field equalities. `demoConfig_complete_content` restates it against
`demoConfig.h1Parse` directly (the field the FSM calls); `demoConfig_h1Parse`
records `demoConfig.h1Parse = h1ParseFn` by `rfl`.

## Status

`lake build Reactor.Config` green, zero sorries. `#print axioms` on all three
theorems: `[propext, Quot.sound]` — a subset of the permitted kernel axioms.
