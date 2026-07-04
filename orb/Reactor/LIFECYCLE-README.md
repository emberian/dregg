# Reactor.Lifecycle — Header rewrite on the response path, Drain FSM on admission

`Reactor/Lifecycle.lean` wires two previously-stranded libraries into the
path that actually runs (`Reactor.step` / `Reactor.serialize`, the proven reactor
of `Reactor/Serve.lean`):

1. the **real Header rewrite algebra** (`Header.run`, `Header/Rewrite.lean`) onto
   the response path, *before* serialize; and
2. the **real Drain FSM** (`Drain.step`, `Drain/Basic.lean`) onto connection
   admission.

Both live on one running entry, `lifecycleServe`. Nothing here re-implements a
header op or a drain transition — the theorems are stated against `Header.run`
and `Drain.step` themselves.

## The running path

```
lifecycleServe d prog input
  = Drain gate (Drain.step d .acceptReq)
      ├─ admitted → some (serialize (rewriteResp prog (baseResp input)))
      └─ refused  → none
```

- `baseResp input := Reactor.demoResp (Reactor.reactorSubs input)` — the response
  the running reactor synthesizes. `reactorSubs` is literally
  `(Reactor.step demoConfig (active mkPlain) (recvInto 0 input)).2`, so `baseResp`
  is real reactor output, not a model.
- `rewriteResp prog resp` — applies a REAL `Header.run` program to `resp.headers`
  (viewed as `Header.Headers` through the trivial `toHeaders`/`ofHeaders`
  coercions; a serializer header pair and a `Header.Field` are the same
  name/value bytes).
- `stdRewrite` — the concrete program: strip the RFC 7230 §6.1 hop-by-hop headers
  (`Header.hopStd`), then install `Server`. Strip first / set last, so the
  installed field is never itself stripped.

The gate runs the reactor **only** when `Drain.step` admits. Once the Drain state
is out of `running`, no reactor step runs on a new request.

## Seam theorems

### `header_rewrite_applied` (the Header seam)

```
(rewriteResp prog (baseResp input)).headers
  = ofHeaders (Header.run prog (toHeaders (baseResp input).headers))
```

The headers the reactor emits are *exactly* the real `Header.run` program applied
to the base response's headers — `Header.run` (proven program interpreter, built
on the `get_remove`/`get_set` locality lemmas) composed with the reactor response
path. Supporting evidence that the algebra genuinely ran on the emitted headers:

- `emitted_has_server` — after `stdRewrite`, `get Server = some serverVal`
  (`Header.get_set_eq` on the outermost `set`).
- `emitted_strips_hop` / `emitted_strips_connection` — after `stdRewrite`, a
  lookup of any hop-by-hop name (e.g. `connection`) is absent
  (`Header.get_set` on a distinct name, then `Header.get_strip_hop`).
- `header_rewrite_deterministic` — the emitted headers are the unique value the
  program yields (`Header.run_deterministic`).

### `drain_no_accept` (the Drain seam)

```
d.mode ≠ .running  →  (lifecycleServe d prog input).2 = none
```

Once the Drain state is draining / drained / closed, the lifecycle admits no new
request: no bytes are served, so the reactor never runs on a new connection.
`Drain.acceptReq_refused_of_not_running` (no accept admitted once draining)
composed with the reactor admission gate. Companions:

- `drain_running_serves` — in `running`, the FSM admits and the served bytes are
  `serialize (rewriteResp prog (baseResp input))` (the full composed path).
- `drain_admit_charges_inflight` — admission advances the REAL Drain accounting
  (`inflight + 1`, via `Drain.running_acceptReq_admits`): the gate is the genuine
  FSM, not a boolean flag.

## Anti-island bridge

`base_serialize_eq_serve`: when the FSM emits no response of its own
(`sendsOf (reactorSubs input) = []`), `serialize (baseResp input) = serve input`.
The un-rewritten base path is literally `Reactor.Serve.serve`; `lifecycleServe`
inserts the header-rewrite stage into that running serve path. This is a stage on
the path the reactor already serves, not a parallel model.

## Verification

- `lake build Reactor` — green (builds `Reactor.Lifecycle`).
- Zero `sorry` / no `UNCLOSED`.
- `#print axioms` on every seam theorem ⊆ `{propext, Quot.sound}` (within the
  allowed `{propext, Quot.sound, Classical.choice}`).

## Files

- `Reactor/Lifecycle.lean` — the lifecycle wiring.
- `Reactor.lean` — imports it (`import Reactor.Lifecycle`).
