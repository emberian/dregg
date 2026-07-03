# deos-viewer — THE DESKTOP IN A LINK

A shared deos desktop is a **tape**, not a screenshot: a pinned genesis instant
plus the message sequence a session sent, encoded into a URL fragment —

```
deos1!ts=<unix>[!tab=<surface>][!root=<64 hex>][!act=<cell hex prefix>:<verb>]…
```

The recipient's viewer boots a FRESH world at the pinned instant, re-executes
the tape through the verified executor, re-derives the canonical ledger root,
and compares it against the root the link claims. The headline of a shared
desktop is an **equality** ("ROOT MATCH"), not an image.

## The three pieces

* **The codec** — `starbridge-v2/src/share_link.rs`: pure, gpui-free,
  fail-closed, round-trip-tested (golden canonical form pinned in tests; the
  format is a compatibility surface — bump `deos1` rather than move it).
* **The server route** — `starbridge-v2/src/main.rs` `serve_ie6_headless`:
  `GET /shared?d=<fragment>` decodes, fresh-boots
  (`world::demo_world_at(ts)`), replays via the real `inspect_act` send path,
  and serves the verdict page; `GET /shared/frame.png?d=<fragment>` renders
  the replayed cockpit in a throwaway headless window (opened → captured →
  removed). Stateless per request; **read-only** — a stranger's link never
  touches the live world and buys at most 32 replayed acts.
* **This page** — the static landing that reads `#deos1!…` (fragments never
  ride the HTTP request), previews the tape client-side (display only — the
  server codec is the authority), and hands it to the reader's own
  `starbridge-v2 --serve-ie6` server as `/shared?d=…`.

## Try it

```
cd starbridge-v2 && cargo run -- --serve-ie6 8600
open "http://127.0.0.1:8600/shared?d=deos1!ts=1751500800"
```

Visit it twice: the same root re-derives (determinism is the point). Bake the
derived root back into the link as `!root=…` to make the claim checkable.

## Honest scope

The replaying server binds 127.0.0.1 — "shareable" today means anyone who runs
deos can paste your link into *their own* viewer. The link format is
server-independent and carries no secrets or capabilities: sharing a desktop
hands over a *derivation*, never authority. Natural next welds: the wasm
cockpit speaking the same fragment (the codec compiles on wasm32 unchanged),
and the live serve-ie6 session recording its own act tape into a Share link.
