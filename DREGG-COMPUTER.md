# HAVE A DREGG COMPUTER — the DreggNet⇄deos vat design

*Fable · 2026-07-03 · design wave `wf_eec2e0e5-f31` (5 scouts + synthesis; the remote-attach
scout hit the schema retry cap and is resumable). Read-only design — no code changed. Full
per-scout maps with file:line anchors are in the workflow journal; this is the synthesis +
the recommended v0 slice.*

> **Product framing (ember):** this is NOT "rent a vat" — it is **"Have a Dregg Computer."**
> Yours, follows you, cannot be lied to, happens to live in the cloud. "Get a Mac," not
> "provision an instance."

All four frontiers ground-truth cleanly against both trees. Here is the synthesis.

---

# ONE VAT ARCHITECTURE + THE v0 VERTICAL SLICE

## What is a deos vat (newcomer explainer)

A deos vat is **your Dregg Computer**: a private, always-there computer that happens to live in the cloud but belongs to *you*, not to the provider running it. Technically it is a single persistent server (`ServerFleet::create`, DreggNet control/src/server.rs:693) whose identity is not a random row-id but a content-addressed **cell** on the deos ledger, derived from `(you, app, name)` (the `cell_id` field, server.rs:56). Because the whole computer is a cell, the things you do *to* a computer come for free: it sleeps by checkpointing its state to a committed root (`checkpoint_root`, server.rs:65), wakes by restoring from it, **forks** into a divergent copy (`World::fork`, starbridge-v2/src/world.rs:695 / server.rs:835), and survives a provider restart because its record reloads from a durable cell store (`ServerStore` reload, server.rs:603). You pay for it by the uptime-period against a funded lease whose admission reads your *real* on-chain reserve, never a self-asserted flag (server.rs:387,437) — so no machine ever runs unpaid, and no provider can bill you for one that didn't.

The reason you can rent it from a stranger is that **it cannot be lied to**. A capability string `vat:<cell-id>` scopes you to exactly your vat and nobody else's — present it to another account's vat and you get an authenticated-but-uncapped 403 (webauth lib.rs:183, `Verdict::Deny { authenticated: true }`). And every action your vat takes emits a receipt you verify against *your own* trust anchor, not the provider's word: at minimum a signed receipt-chain (`verify_receipt_chain_with_keys`, turn/src/verify.rs:245), and at the strong end a STARK the provider physically cannot forge because verification pins a verification key from honest setup that is never read from the provider's artifact (lightclient/src/lib.rs:169-176). You can even tell your vat to run cheap and defer its cryptographic witnesses (`WitnessMode::Symbolic`, turn/src/collapse.rs:98-114) — the state transition and every admission gate still fire; only the publishable proof is deferred, and a later **collapse** re-derives the real witnesses fail-closed (world.rs:1390-1398). Cheap-but-not-yet-checkable, or proof-as-you-go: you pick, and the provider can't cheat either way.

## The coherent architecture: everything is a cell on one World

The four frontiers are not four features — they are four layers over a **single thesis**: *the vat, its contents, and its agents are all cells on one deos `World`, scoped by one capability grammar, made trustable by one witness discipline, metered by one settlement rail.*

| Layer | What it is | Real substrate (WORKS) |
|---|---|---|
| **Substrate** (F1) | the vat = a ServerFleet persistent server = a cell | `ServerFleet::create/launch` server.rs:693; identity=cell_id server.rs:56; fork server.rs:835; wake/sleep=checkpoint_root server.rs:65; reload server.rs:603 |
| **Rental** (F1) | funded-lease admission + per-period settle | real reserve read server.rs:387,437; exactly-once per-period settle server.rs:1108 |
| **Scoping** (F1+webauth) | `vat:<cell-id>` capability | `decide()` flows arbitrary cap through `grant::cap_context` webauth lib.rs:183; deny=authenticated:true |
| **Trust** (F2) | witness mode + client-side verify | `WitnessMode` collapse.rs:98-114; `is_deferred` collapse.rs:88; `verify_receipt_chain_with_keys` verify.rs:245; `verify_history` lightclient lib.rs:186 |
| **Contents** (F3) | your cells/services/grains as one Home | World census world_explorer.rs:171; Service Directory; grain=cell weld (design) |
| **Killer app** (F4) | persistent/forkable hermeses in the vat's World | `AgentMemoryCheckpoint::capture/resume` agent_memory.rs:121,170; `hire_resident` resident_agent.rs:162 |

The unification is literal, not metaphorical: a **grain is a cell** (its `/var` is a cell umem heap → content-addressed `data_root`, DreggNet sandstorm-bridge/src/cell.rs:75), a **hermes is a cell** (its working set is a witnessed `UProjection`, agent_memory.rs:121), and the **vat is a cell** (server.rs:56). So one `vat:<id>` / cell-cap grammar scopes all of them, one Full/Symbolic+collapse discipline makes all of them checkable, and one funded-lease rail meters all of them. This is the coherence layer the ~47 organs were missing a single "why" for.

## THE single recommended v0 vertical slice

**"Rent a Dregg Computer, hold a key that reaches only yours, see its cells, verify one of its receipts against your own key, restart the provider — it followed you."**

This is the **F1 rental trunk with F2's receipt-verify grafted on**, plus a thin F3 read. It is the smallest end-to-end thing that exercises rent + scope + see + verify + persist, and it is ~90% assembly of pieces that already work. One command:

```
dregg-cloud vat create --name mybox
  → "Your Dregg Computer 'mybox' is up.
     endpoint: http://127.0.0.1:PORT   id: <cell-id>   key: dga1_…"
```

What the renter does in one sitting, and which property each step proves:

1. **HAVE A VAT** — the command returns an id + endpoint (not "provisioned an instance"). Reuses `ServerFleet::create`+`launch` over `LocalProvider` behind the funding gate (server.rs:693; funding authorize server.rs:387).
2. **SCOPED TO YOU** — `curl -H "Authorization: Bearer <vat-key>" .../v1/vats/<cell-id>` returns your vat's live state; the *same key* against a second account's vat id returns **403 authenticated-but-uncapped**. Zero new crypto — `decide()` already admits iff the cred was granted that exact `vat:<id>` (webauth lib.rs:183).
3. **SEE YOUR CELLS** — `GET /v1/vats/{id}` returns the vat World's census (cells + balances + receipts), reusing the World Explorer reader (world_explorer.rs:171). This is the cheap stand-in for "see my remote cells."
4. **VERIFY A RECEIPT** — `dregg-cloud verify` runs `verify_receipt_chain_with_keys(receipts, &[executor_pk])` (verify.rs:245): green. Flip one byte → red (the tamper test already exists, verify.rs:538). This is the "cannot be lied to" property made tangible.
5. **IT PERSISTS** — restart the control-plane process; `dregg-cloud vat list` still shows 'mybox' (`ServerStore` reload, server.rs:603). The computer followed you.

## Build order (dependency-sorted)

1. **`ServerRecord.endpoint: Option<String>`** — the one missing field; populate on bring_up (loopback addr in dev), persist + carry through reload. Same `#[serde(default)]` back-compat pattern as `machine_id`/`cell_id` (server.rs:38,56). *Confirmed absent* (no `endpoint:` in server.rs). **2-3h. Foundation — everything reachable hangs off it.**
2. **`grant::vat_cap(cell_id) -> "vat:<id>"`** + one `attenuate_caps` call at provision (webauth grant.rs). No-amplify keeps the `acct` caveat so the cred still resolves to the owner. **1h. Zero core-verify change.**
3. **`POST /v1/vats` + `GET /v1/vats/{id}`** gateway handlers over `ServerFleet`, behind `FundingSource::authorize` (fail-closed on missing `X-Dregg-Subject`, mirroring api.rs). **5-7h. The main weld.**
4. **`required_cap` → `vat:<id>`** for the vat path (set `?cap=` before forward-auth, or a per-vat host-map entry, webauth config.rs:170). **2h.**
5. **Wire `ServerFleet` as the `/api/servers` `ServerSource`** — the trait is an explicit unwired seam ("absent ⇒ the surface is empty," api.rs) — so `vat list` is real and subject-scoped. **2h.**
6. **`dregg-cloud verify`** — `verify_receipt_chain_with_keys` + an explicit `is_deferred` gate (collapse.rs:88) so a symbolic receipt is refused as a non-commitment rather than passing vacuously. **3-4h.**
7. **`dregg-cloud vat {create,list,verify}` CLI verbs** — extend cli/src/cloud.rs, which already speaks the gateway over `Authorization: Bearer <dga1_>` (currently only `/v1/apps/{app}/machines`). **3h.**
8. **End-to-end demo + the cross-account 403 test + byte-flip red test.** **2-3h.**

**Total ~20-26h.** (Pure F1 trunk ~14-20h; the F2 verify graft adds ~4-6h and is what makes the slice *prove the idea* rather than just provision a box.)

## Honest gaps — what v0 deliberately does NOT do

- **Web starbridge roaming is not real in v0.** "Connect from anywhere and your stuff is there" is **FALSE for the web build**: the wasm world is always ephemeral (session.rs gates resume off wasm). v0 proves scoping from *any HTTP client* (curl/CLI as the starbridge stand-in); the actual web-build world resolution via `web_of_cells` against a hosted durable image is the named follow-up.
- **LocalProvider only.** `Ec2Provider` is argv-real/API-stub (provider.rs); the endpoint is the dev loopback, not an overlay-routed URL. Live Firecracker boot is the reviewed-go step (server.rs:50-54).
- **Two leases still unreconciled.** v0 meters via `ServerFleet`'s in-memory per-period settle (server.rs:1108); the richer on-chain, light-client-witnessable `HostedLease` (DreggNet lease/src/lib.rs:31) is *not* the one billing the vat. Unifying them is deferred.
- **Witness mode is not on the lease yet.** Grep of DreggNet lease/exec/control for `witness_mode`/`Symbolic` is **ABSENT**. v0 ships **Full-mode verify only** (the green/red demo). The Symbolic toggle + collapse-request endpoint (F2's full slice) is the immediate next increment — cheap, because `WitnessMode`, `collapse`, and `is_deferred` all already work on the deos side (collapse.rs, world.rs:1353).
- **v0 verify trusts the executor key, not a STARK.** `verify_receipt_chain_with_keys` is the ed25519 signed-chain layer. The trust-*minimizing* path (`lightclient::verify_history`, needs only the renter's own VK anchor) is fully built (lightclient/src/lib.rs:186) but **not wired to DreggNet at all** — the F2 stretch.
- **No first-class Vat billing line.** `BillableResource` has no `Vat` variant; v0 reuses `Server` uptime + the existing HostingReceipt→Invoice adapter (billing/src/lib.rs:98-120). A `Vat` variant is a follow-up.
- **The killer app (F4) is post-v0.** Hermes persistence is **PARTIAL**: the cell survives on the durable World, but the *living* loop drops on restart because the gateway rides a `Box::leak`'d `'static AgentRuntime` (resident_agent.rs:194) and there is no `rebind_resident`. `console/src/model.rs` has `AgentView` (:99) but **no `HermesView`** and no spin/fork/resume action endpoints. The persistent/forkable-hermes management console is the payload the v0 substrate is built to carry, not v0 itself.
- **Grains (F3) are a prototype.** DreggNet `GrainCell` self-describes as "before the production weld" (sandstorm-bridge/src/lib.rs:6); the grain-as-cell unification is a native deos design (`seed_grain_cell`), not built.

**The through-line:** ship the F1 trunk + F2 verify first because it is the smallest thing that makes "you HAVE a Dregg Computer that cannot be lied to" literally true and demoable, and because it lays the exact substrate — a scoped, reachable, verifiable, persistent World-as-a-cell — that F3's Home surface and F4's living hermeses then ride without re-architecting anything.

---

## Per-frontier ground truth (WORKS / STUB / ABSENT, condensed from the scouts)

### THE RENTAL SUBSTRATE — how you rent, pay for, and are authorized to a private vat (your Dregg Computer): the lease that meters+bills its execution, the webauth capability that scopes the renter to THEIR vat, and the provision→endpoint flow.
- **Exists:** Three real-but-DISJOINT pillars, plus one real substrate that is the actual "vat". Citations are DreggNet unless noted.

LEASE (metering). `HostedLease` (lease/src/lib.rs:31-102) — WORKS, tested end-to-end (:123-153). It is a durable-execution lease built on `starbridge_execution_lease` (:22-26): a `StandingObligation` rent meter (`meter(period_index, clock)` :54), a durable execution image = the lease cell's umem heap `EXEC_COLL` advanced by `checkpoint(new_digest, working)` (:62-68) on a `Monotonic` cursor, and a lapse audit `lapse_if_behind` (:72) that reclaims a delinquent slot. This is the richest "meter a vat's execution over time" primitive — but it is a STANDALONE cell abstraction, wired to NOTHING that provisions a machine.

A SECOND, lighter lease exists and is the one actually used by control/gateway: `dreggnet_bridge::Lease` (funded bool / budget_units / per_period_units / cap_grade), re-exported at control/src/lib.rs:108. The two lease notions are NOT unified (design gap).

BILLING (invoicing over the meter). billing/src/{invoice,limits,estimate,usage}.rs — WORKS as a library, dev-dep-tested against the REAL meter (billing/src/lib.rs:67-204). Receipt-traced sealed invoices (`Invoice::verify_against_receipts`), `BudgetGuard` hard-cap + 50/80/100% alerts over the audited `ReplenishingBudget` (limits.rs:105-208), estimate-before-you-deploy (estimate.rs:58). Metering u
- **Gap:** To make "rent a private vat" real, five welds are missing:

1. NO VAT ENDPOINT. `ServerRecord` (server.rs:119-180) and gateway `Machine` (`private_ip=""`, gateway.rs:304) carry no reachable address. A renter provisions a vat but gets nothing to talk to. Missing: a stable per-vat endpoint (mesh IP:port of the backend machine, or a gateway-routed URL keyed by the vat's cell-id) persisted on the record.

2. NO PER-VAT CAPABILITY. webauth caps are web-surface strings (grant.rs:23-35); there is no `vat:<cell-id>` grammar and no minting of a renter credential scoped to exactly one vat. Missing: `grant::vat_cap` + a mint that attenuates the account session down to their vat.

3. SERVERFLEET NOT EXPOSED THROUGH THE GATEWAY. `/api/servers` `ServerSource` is unwired (api.rs:104-107); there is no `POST /v1/vats` create/launch verb over `ServerFleet`. The persistent-vat substrate is unreachable from
- **v0 slice:** SMALLEST demoable v0: one CLI command turns a paid+authed account into a reachable, exclusively-scoped Dregg Computer.

`dregg-cloud vat create --name mybox` (extend cli/src/cloud.rs, which already speaks the gateway over `Authorization: Bearer <dga1_>`):
  → gateway `POST /v1/vats` with the account session credential
  → funding gate authorizes a funded lease for the subject (funding.rs:74)
  → `ServerFleet::create` + `launch` over `LocalProvider` (real in-process backend, period-1 pre-paid: server.rs:1030-1064)
  → assign `endpoint` (loopback addr in dev), mint the `vat:<cell-id>`-scoped credential (attenuate_caps)
  → returns, and the CLI prints:
      "Your Dregg Computer 'mybox' is up.

- **Risks:** Endpoint reachability is the real unknown: v0 uses the LocalProvider loopback addr, but a genuinely REACHABLE-from-any-starbridge vat needs the overlay-routed data plane (control/src/mesh.rs TailscaleMesh + a gateway reverse-proxy keyed by cell-id) — that live fleet boot is the named reviewed-go step (server.rs:50-54) and is where 'have a computer in the cloud' actually becomes true. · Two-lease reconciliation is deferred: v0 bills via ServerFleet's in-memory per-period settle, so the vat's rent is NOT yet the light-client-witnessable HostedLease obligation the lease crate proves. Until unified, the 'provider physically cannot lie' guarantee holds for execution witnesses but not for the rent meter. · Per-vat required_cap resolution: minting a `vat:<id>` cred is trivial, but the forward-auth edge must map each /v1/vats/{id} request to `?cap=vat:{id}`. If the gateway sets that query itself it must be un-forgeable by the client (bind :8080 internal, as api.rs:30 already warns) or a caller could downscope the required cap. · WitnessMode symbolic/full is absent from LeaseTerms/Lease entirely — the renter cannot pick cheap-verify-later vs proof-as-you-go on the rental object; that product promise has no representation on this frontier yet. · ServerFleet's COMPUTE-AS-CELL fork/wake persist the boundary-root COMMITMENT but the reified in-sandbox image across a control-plane restart is a named Stage-B seam (server.rs:635-640) — so 'resume its full working set after restart' is partial (durable identity+root, not yet the durable process image).

### WITNESS MODES + THE TRUST MODEL — why renting a Dregg Computer from a stranger is safe. The renter picks how their vat witnesses (cheap Symbolic / defer-verify-later vs proof-as-you-go Full), and runs a client-side check that lets them trust an untrusted provider because the provider physically cannot forge a verifying proof of their vat's history.
- **Exists:** THE WITNESS-MODE SUBSTRATE — WORKS (deos side), ABSENT (DreggNet side).

WitnessMode enum: `turn/src/collapse.rs:98-114` — `Full` (`#[default]`, every commit materializes the per-turn Merkle witness via `Ledger::root()`, receipt immediately publishable) and `Symbolic` (state transition fully applies but witness deferred; receipt carries the all-zero sentinel). `as_u8`/`from_u8` wire encoding at :122-138 (unknown byte → Full, the safe default). WORKS.

Deferred sentinel + detector: `turn/src/collapse.rs:81-90` — `DEFERRED_STATE_HASH = [0u8;32]`, `is_deferred(receipt)` true iff both pre/post state hashes are the sentinel. WORKS.

World wiring: `starbridge-v2/src/world.rs:207-213` (`witness_mode` field + `symbolic_turns: Vec<Turn>` buffer), default Full at :281-282. `set_witness_mode` at :1328-1331 (flips both World and engine executor). `is_symbolic`/`symbolic_pending` at :1298-1305. Symbolic commit path at :1146-1183 — buffers the turn, skips the replay-tape double-execution, and (for a durable world) is blocked from persisting a deferred receipt (:1183). Fork always resets to Full (:764-769). WORKS.

collapse (World): `world.rs:1353-1403` — drains the buffer, re-runs each turn through `History::record_commit` on the Full recorder, overwrites the deferred receipt in the provenance log with the real one, then FAIL-CLOSED at :1390-1398: `canonical_ledger_root(engine) != canonical_
- **Gap:** Three gaps between the working substrate and the "safely rent a Dregg Computer" product:

1. NO WITNESS-MODE VAT SETTING. `WitnessMode` is a per-`World`/per-executor runtime flag (`world.rs:1328`), but the vat/lease that DreggNet provisions (`HostedLease`, `LeaseTerms`) carries no mode. A renter cannot choose cheap-symbolic vs proof-as-you-go Full at provision time, and the provider has no sealed record of which the renter paid for. The choice must become a durable vat setting the meter/pricing and the checkpoint path read.

2. NO CLIENT-SIDE VERIFY PATH FOR THE RENTER OF THE STRONG (STARK) KIND. DreggNet's only shipped verify (`console/src/verify.rs`) re-witnesses the ed25519-SIGNED receipt chain — which trusts the provider's executor signing key (a provider can sign a chain it fabricated as long as it never contradicts itself). The `lightclient` crate is the trust-MINIMIZING path (need
- **v0 slice:** A renter picks a witness mode when spinning up their Dregg Computer, and can verify a receipt it returns — trusting only their own anchor, not the provider.

Concretely, the smallest demoable thing: the console vat-provision panel gets a two-choice mode toggle ("Cheap — verify later (Symbolic)" / "Proof-as-you-go (Full)") that writes `witness_mode` into `LeaseTerms`/the lease cell. After the vat runs a turn, the console's existing Verify affordance (`DreggNet/console/src/verify.rs`) becomes mode-aware:
 - Full vat: click Verify ⇒ green "re-witnessed: chain ✓, signature ✓ against YOUR anchor" (reuse `verify_receipt_chain_with_keys`, and where the aggregate is present, `verify_history`).
 - Sy
- **Risks:** TWO TRUST LAYERS, DIFFERENT STRENGTHS — do not conflate them. DreggNet's shipped verify (console/src/verify.rs) is the ed25519 SIGNED-receipt-chain layer: it trusts the provider's executor signing key (a provider can sign a self-consistent fabricated chain). The trust-MINIMIZING claim ('provider physically cannot lie') rests on the STARK lightclient path (verify_history against the renter's own VK anchor), which is feature-gated (`#![cfg(feature = "prover")]`) and NOT wired into DreggNet at all. Marketing the strong claim while shipping only the signed-chain verify would be dishonest — the v0 must be explicit about which guarantee the green checkmark represents. · SYMBOLIC + verify_receipt_chain IS A VACUOUS-PASS FOOTGUN. Two consecutive deferred receipts have all-zero pre/post state hashes, so the continuity check `pre == prev.post` (turn/src/verify.rs:167) passes trivially (0==0) while attesting NOTHING. Any renter-facing verify MUST call `is_deferred` (collapse.rs:88) and refuse before reporting a symbolic receipt as verified. · COLLAPSE IS IN-PROCESS ONLY. World::collapse needs the resident recorder ledger + record_exec; a remote renter cannot drive it and must ask the (untrusted) provider to collapse, or run collapse_with themselves — which requires data availability (holding the turns + pre-state ledger). Without the DA retrieval path (lightclient/src/lib.rs:71-90) actually wired, 'collapse to verify' still leans on the provider to hand over honest inputs; the independence claim needs the DA side too. · ANCHOR DISTRIBUTION IS THE WHOLE BALLGAME. verify_history is only sound if the RecursionVk anchor and committee keys reach the renter from trustworthy genesis/epoch config, NEVER from the vat (lightclient/src/lib.rs:169-176). DreggNet has no such distribution channel today; if the console fetches the anchor from the same host that runs the vat, the entire trust model collapses to 'trust the provider.' · MODE-DOWNGRADE / BILLING INTEGRITY. Unless witness_mode is persisted INTO the checkpointed lease image (not just a runtime flag), a provider could bill a renter for Full while running cheap Symbolic. The setting must be witnessed in the lease cell heap so a downgrade is itself a detectable forge, and the collapse fail-closed convergence (world.rs:1390) is the backstop that a symbolic run cannot have admitted anything a Full run would refuse.

### YOUR SERVICES + GRAINS ON YOUR DREGG COMPUTER — the Athena payoff: running services (durable containers, Sandstorm grains) and files surfacing as ONE navigable "home directory" of cells you own in starbridge, reachable when you connect from anywhere.
- **Exists:** The pieces exist but on two disconnected sides, and NONE compose into a unified home.

DEOS SIDE (starbridge-v2, the desktop you actually run):
- App Shelf — WORKS. `starbridge-v2/src/deos_desktop/app_shelf.rs:173` `install_on_world` launches any of ~20 composed deos apps onto the LIVE World as a real cell (`InstalledApp` :81, cell on `World::ledger()`, install receipt in `World::receipts()`); `icon_face` :153 gives a launched app its own desktop face. But it launches deos-NATIVE apps only, not grains/services.
- Service Directory — WORKS. `service_directory.rs:157` `discover()` scans `World::ledger()` and lists every cell whose program publishes an interface (`InterfaceDescriptor::derive_replayable`), with a real ANNOUNCE turn (:236). Only surfaces ledger cells that do method-dispatch.
- Service Explorer — WORKS. `service_explorer.rs` Postman: pick a published method, invoke as a verified turn (no new kernel effect).
- Durable home image — WORKS (tested `durable_desktop.rs:379`). `boot_desktop_world` (:178) makes "your world is one durable redb image": close/reopen lands EXACTLY where you were.
- Session/roaming front door — WORKS but native-only. `session.rs:1022` `open_session_world` opens a per-user durable image; `SessionRecord` (:527) + `login_resumable` (~:630) resume the cap-tree on relaunch. CRITICAL SEAM: the durable image is a LOCAL redb file; the wasm/web starbridge
- **Gap:** Three concrete missing welds:

1. NO UNIFIED HOME SURFACE. There is no place that shows Files (your cells) + Apps + Services (durable) + Grains as ONE navigable, cap-scoped surface. World Explorer is read-only, cells-only, and types cells by a balance heuristic (`world_explorer.rs:171`); App Shelf is deos-apps only; Service Directory is ledger-service-cells only. The Athena "here is my whole environment" view does not exist.

2. GRAINS/SERVICES ARE NOT CELLS ON YOUR DEOS WORLD. `GrainCell` (DreggNet `grain.rs:92`) already has the exact shape of a ledger cell (id + data_root + lifecycle state + owner), and a durable workflow (`durable/`) is a running service — but neither is projected onto the deos `World::ledger()`, so neither can be owned, inspected, or roamed as a cell in starbridge. The two repos are separate workspaces with no dep edge, so nothing bridges them.

3. ROAMING IS NATIVE-
- **v0 slice:** "MY STUFF IS HERE WHEN I RECONNECT," on the native durable desktop (which already persists — durable_desktop.rs:379).

What the user sees/does: opens the desktop → a new "Home" window shows their cells grouped Files / Apps / Services / Grains. At boot the desktop seeds ONE grain cell via `seed_grain_cell` (e.g. an "Etherpad" grain: state=Sleeping, a committed data_root) alongside the existing demo cells and one App Shelf install. So Home shows all four kinds at once: their data cells (Files), the launched app (App), a service-publishing cell (Service), and the Etherpad grain (Grain · Sleeping · data_root shown). They close the desktop and reopen it — because the grain cell was committed onto
- **Risks:** CROSS-REPO MIRROR TRAP: deos (breadstuffs) and DreggNet are separate cargo workspaces with no dep edge (grep confirms zero dreggnet/sandstorm refs in starbridge-v2). v0 must reconstruct the grain-cell convention NATIVELY in deos from the real GrainCell fields (grain.rs:92 — cell_id/owner/spec/data_root/state/metered_units), not import sandstorm-bridge. Paste those exact fields into any subagent prompt or it will invent a mismatched shape. · GRAIN 'RUNNING' IS ASPIRATIONAL: sandstorm-bridge is an explicit prototype (lib.rs:6 — a NotesApp handler, welded to dreggnet-webapp, not real containers). Home can show lifecycle state honestly, but 'a service that is actually running and survives restart' needs the real dreggnet-exec+durable backend. Do not let the UI imply a live container in v0. · ROAMING OFF-MACHINE IS A BACKEND INTEGRATION, NOT A DEOS-ONLY CHANGE: the durable home is a local redb file and wasm resume is gated off (session.rs ~:617). True 'follows you' needs the hosted durable image + dregg:// verified read (starbridge-web-surface::web_of_cells + DreggNet durable/console). Keep it as the named follow-up; do not fake a web home over the ephemeral wasm world. · CAP-SCOPING IS LOAD-BEARING: the home MUST project only cells the session root cap reaches (session.rs granted c-list), echoing the grain L6 tenant partition (tenant.rs / grain.rs:116). A naive full-ledger scan (like Service Directory's discover, service_directory.rs:157) would leak other principals' cells into 'your' home. · DON'T DUPLICATE CLASSIFIERS: World Explorer already types cells by a balance heuristic (world_explorer.rs:171). The new File/App/Service/Grain classifier should become the shared one, or the two surfaces will disagree on what a cell IS.

### THE KILLER APP — PERSISTENT / RESUMABLE / FORKABLE / EXPLORABLE HERMESES + THE MANAGEMENT CONSOLE. A rented AI agent (hermes) that LIVES in your Dregg Computer: persists across restart, resumes its working set, forks into divergent worlds you stitch back, and is explorable via receipted activity + provenance — plus a designed cloud console to spin/fork/resume/explore/bill it (not xterm-on-a-page).
- **Exists:** The four verbs, ground-truthed:

RESUME — WORKS (as model + desktop UI). `starbridge-v2/src/agent_memory.rs:121 capture` projects a live agent cell's whole working-set (fields/balance/nonce/heap/caps) into a witnessed umem `UProjection`; `:170 resume_into` / `:201 resume_into_fresh_world` reify it back FAIL-CLOSED behind four teeth — root tooth (`:174`), reprojection drift (`:185`), identity (`:189`), reify class. Live round-trip proven on a real confined deos-js agent (`agent_attach.rs:276 live_agent_memory_checkpoint_resume_continues`, tamper-refusal `:365`). Wired into the cockpit UI: `cockpit/panels_workspace.rs:2200 agent_memory_checkpoint` + `:2233 agent_memory_resume` (buttons, status strings, teeth re-witnessed at `:2248`).

EXPLORE — WORKS. `agent.rs:142 AgentActivity::build` reads mandate edges (`:150`), receipted actions with refusals interleaved in true order (`:209 build_actions`), and an authorization CAN/CANNOT boundary (`:305`), all from the live `World` (never self-report). Rendered by the Agent Room (`deos_desktop/agent_room.rs` — WHO/WHAT/MANDATE/REACH faces). Provenance Walker (`deos_desktop/provenance_walker.rs`) re-derives each receipt link (state chain + blocklace back-edge, `LinkVerdict` at `:94`), painting Verified/Broken/Deferred/Reseeded. Gate refusals merge as REFUSED rows (`hireling.rs:358 merge_refusals_into`).

FORK — WORKS as substrate, unglued f
- **Gap:** 1. HERMES PERSISTENCE. Nothing checkpoints the LIVING hermes beyond its cell umem. Missing: a `HermesManifest` = (durable World image ref) + (`AgentMemoryCheckpoint` of the resident cell) + (a NEW `GatewayCheckpoint`: `session_id`, mandate, brain label, `StepPlanner.next`, and the `GrantRegistry` per-tool budget counters + clock). Those gateway budget counts are NOT exposed/serializable from deos-hermes today.

2. REHYDRATE ON RESTART. `hire_resident_seeded` always genesis-mints a FRESH cell; there is no `rebind_resident(world, existing_cell, mandate, gateway_ckpt)` that re-attaches an `AgentHandle` to an ALREADY-LIVING cell and restores budgets. So a recovered World cannot re-staff its room. No `HirelingState::rehydrate()` reading manifests at boot.

3. FORK-A-HERMES FLOW. The substrate exists (`World::fork`, `BranchStitchSession`) but no glue: `fork_hermes(handle) -> (HermesFork, Herme
- **v0 slice:** SMALLEST demoable "a hermes runs in my Dregg Computer, survives a restart, I fork it, and I watch its receipts in a designed panel" — done on the DESKTOP (starbridge) where the most already works, then a thin console card:

1. HIRE a resident + STEP it 2-3 beats (WORKS today: real receipted turns on the durable World, `hireling.rs`).
2. On step, write a `HermesManifest` (cell id + mandate + planner index + gateway budget snapshot) to the durable sidecar (World cell/receipts already persist via `durable_desktop`).
3. RESTART the desktop: `durable_desktop` recovers the World (cells+receipts return), then NEW `HirelingState::rehydrate` re-binds the resident onto its living cell and re-staffs th
- **Risks:** TWO-EXECUTOR BUDGET DRIFT: gateway rate/budget counters live on the Box::leak'd `AgentRuntime` (resident_agent.rs:194), a DIFFERENT executor than the durable World. Persisting/rehydrating them needs a new deos-hermes surface (GrantRegistry snapshot/rehydrate) that does not exist; a mismatch between persisted counts and reality silently mis-meters. This is the load-bearing new seam. · RESUME ≠ MEMORY-OF-THOUGHT: AgentMemoryCheckpoint captures the cell's LEDGER working-set (fields/balance/nonce/heap/caps), not the hermes' conversation/scratchpad. The brain is stateless per-prompt today (resident_agent.rs:240 mints a fresh brain), so nothing is lost NOW — but a real resumable LLM hermes needs a conversation-context umem plane too; claiming 'resumes its working set' is honest only for the ledger footprint. · LEAKED RUNTIME ON REHYDRATE: every hire/rebind Box::leak's a `'static AgentRuntime`; rehydrating N residents on boot leaks N runtimes (named teardown seam in hireling.rs:37). Fine for a demo, a real cloud host needs a lifecycle-owned runtime pool. · FORK IDENTITY AMBIGUITY: both forks share the resident's cell id (world.fork clones the ledger); provenance must disambiguate by World, not cell. And 'pick the winner' has no UI — branch_stitch settlement gate is proven for state, but the human/agent choice of which fork to stitch is unbuilt. · WEB LIFECYCLE BRIDGE IS REAL BACKEND WORK: agent-host serves SSH-forced-command attach sessions, not web-driven spin/fork/resume; console is a read-mostly server-render aggregator. Wiring console buttons → control/agent-host → a live resumable hermes crosses crates that don't currently talk, and the console's `AgentView` is a one-shot deploy report, not a living session.



---

# REMOTE ATTACH — the completed design frontier

*(the scout that capped on schema, redone free-text; folded in here.)*

All ground truth gathered. Here is the design, as the lane's final free-text answer.

---

# REMOTE ATTACH — the starbridge points at your Dregg Computer, and your World follows you

*Scout ground-truth + design. All paths relative to `/Users/ember/dev/breadstuffs/.claude/worktrees/deos-night-shift/`.*

## GROUND TRUTH — what the starbridge can already do against a remote node

### The desktop DOES connect to a remote node today, and reflects it live — read-rich, write-capable in the client, write-wired only in one view

**The attach path is real and threaded end-to-end.** `--node <url>` / `--node=<url>` parses at `starbridge-v2/src/main.rs:838` (`node_url_arg`), rides through the login ceremony (`login.rs:53,100` — `LoginSurface::boot(…, node_url, …)`, main.rs:950) into `Cockpit::with_node` (`cockpit/construct.rs:39`), which at construct wraps a real client, opens the SSE stream, and takes one snapshot (`construct.rs:282-293`). All best-effort: an unreachable node leaves the embedded image fully usable.

**Reads — WORKS, and renders remote identically to local.** `NodeClient` (`client.rs:25-162`) speaks the full read contract: `/status`, `/api/cells`, `/api/receipts` (typed + tolerant-raw), `/api/federations`, `/api/blocklace/blocks`. The wire contract is deliberately hand-mirrored in `model/mod.rs:1-13` ("a *protocol* dependency, not a *code* dependency"). `LiveNode::sync` (`client.rs:577`) projects snapshots through `LiveReflection` (`live_node.rs:194-295`) into the SAME uniform `Inspectable` the embedded world uses — "no parallel view path" is a stated invariant (`live_node.rs:19-23`).

**Live events — WORKS.** A background thread pulls `/api/events/stream` (`sse_reader_loop`, `client.rs:680-755`), auto-reconnecting with the `Last-Event-ID` header, feeding the **pure, wasm-safe** `SseParser` (`live_node.rs:60-182`, byte-fixture tested) into `ReceiptFeed` (`live_node.rs:309`, dedup-by-`chain_index` + resume cursor). The cockpit drains it per frame (`cockpit/live.rs:13`) and renders the LIVE NODE strip (`panels_main.rs:67`), a remote data-plane strip in devtools-network (`panels_devtools.rs:262`), and wire-backed live federations (`panels_devtools.rs:688`).

**Writes — the client can submit turns remotely, on two real paths:**
- **Operator path:** `unlock` (`POST /cipherclerk/unlock` → bearer, `client.rs:175`) then `submit_turn` (`POST /turn/submit`, `client.rs:217`) — the node signs as its own cipherclerk; refusals in-band.
- **Client-signed path (the important one):** `submit_signed_turn` (`POST /turns/submit`, `client.rs:246`) posts a postcard `dregg_sdk::SignedTurn` under the **user's own ed25519 key** — the node verifies the signature, requires `agent == derive_raw(user_pubkey, blake3("default"))`, runs the same gates, commits under the CLIENT's authority. Plus `faucet_materialize` (`client.rs:270`) to birth a fresh user cell.

**But the interactive write wire lives only in `UnifiedBootView`**, not the main cockpit. `unified_boot.rs:200-251` installs the editor's own Cmd-S save callback to fire `client_signed_save` (`unified_boot.rs:452` — federation-id derivation, chain-head stamping, `valid_until`, the before→after receipt-count proof, agent==user assertion), threading the logged-in user's `signing_seed` (`login.rs:335`). It is exercised by the three bakes (`--render-unified-boot` / `--render-client-signed-turn` / `--render-interactive-node-save`, `main.rs:590-639`). The main cockpit's live-node surfaces are **read-only reflection** — no submit affordance anywhere in the strip/devtools; its TurnComposer targets the embedded world.

**A designed scoping layer already exists and is tested:** `remote_mirror.rs` + `remote_mirror_live.rs` — a **MirrorCap** over a remote cell with a genuine attenuation lattice (depth `Structure ⊑ ReadState ⊑ Live` × the real `AuthRequired` rights axis), read-only by construction (`viewSurface_confers_no_edge`), live tail projected to exactly the receipts naming the mirror's cell, transport-abstract (`RemoteImage` trait; the named production binding is `LiveNode`). This is the cap grammar for "reflect your remote cells" — built, headless-tested, **unwired to any real vat**.

### The web build does NOTHING remotely (against a node)

- The gpui web cockpit boots the real `Cockpit` with **`node_url = None`, explicitly** (`web/src/cockpit_web.rs:112` — "no remote-federation panel on the web boot — the data plane is the in-tab executor"). The JSON/atlas skin (`WebImage`, `web/src/lib.rs:39`) boots a fresh in-tab `demo_world()` — ephemeral, local, no wire.
- Transport is structurally absent on wasm: `live-node = ["dep:reqwest"]` (`Cargo.toml:299`) and the web crate builds starbridge-v2 **without it** (`web/Cargo.toml`: `default-features = false, features=["embedded-executor"]`), so `NodeClient::Http` hits the honest "feature off" bail stubs (`client.rs:369-392`). The SSE reader is `std::thread` + blocking reqwest — impossible on wasm as written.
- The only live socket the web build has is the PTY-over-WebSocket terminal backend (`web/src/pty_ws.rs`) — a terminal bridge, not the node contract.
- Roaming is gated off: "the browser/wasm image is always ephemeral… the resumable surface is gated off wasm" (`session.rs:621-624`; `login_resumable` is `#[cfg(not(target_arch = "wasm32"))]`).
- **Crucially, key custody compiles on wasm:** `embedded-executor` pulls `dregg-sdk` (`Cargo.toml:320`) and the web crate builds it — so `AgentCipherclerk` **client-side signing works in the browser today**. The web gap is transport + custody UX, not crypto.

### The vat side has no door yet (re-confirmed)

No `endpoint` field on `ServerRecord` (grep of `dreggnet/control/src/server.rs` — absent); gateway `Machine.private_ip = ""` (`gateway/src/gateway.rs:304`); no `vat:` grammar in `webauth/src/grant.rs` — but `decide()` flows any `required_cap` string through `grant::cap_context` with the 401/403 split already correct (`webauth/src/lib.rs:63-79, 188-203`).

---

## THE DESIGN — attach = a ticket, a credential, and the node wire contract you already speak

**The one-sentence thesis: the vat's data plane should BE the node wire contract, so the attach is `NodeClient` pointed through the gateway with a `vat:<cell-id>` credential — the desktop starbridge needs a header, not an architecture; the web starbridge needs a transport, not a model.**

### 1. The VatTicket — "your computer's address, the key that reaches only yours, and the anchor you check it against"

One attach handle, printed by `dregg-cloud vat create`, stored in the keychain, shareable as a URI:

```
VatTicket {
  vat_cell_id:  <32-byte cell id>          // the identity — content-addressed from (you, app, name)
  endpoint:     https://gw.host/v1/vats/<cell-id>/node   // the gateway-routed data plane
  credential:   dga1_…                      // webauth cred carrying cap `vat:<cell-id>` (+ acct caveat)
  anchor:       executor_pk (v0) / RecursionVk (stretch) // what receipts verify against — NEVER fetched from the vat
}
```

URI form `dregg-vat://<cell-id>@<gateway-host>` — the cell-id in the address IS the integrity check, the same self-certifying-address argument `web_of_cells.rs` already makes for `dregg://` (the address is the identity; a wrong host cannot forge a matching receipt chain). **"Follows you" falls out of content addressing:** the vat's cell_id derives from `(you, app, name)`, so any starbridge that holds your credential can *recompute* the id and ask the gateway's finder (`GET /v1/vats?subject=me` — the unwired `ServerSource` seam, `api.rs:104-107`) for the endpoint. You never bookmark a machine; you derive your computer.

### 2. The wire path and the two-credentials problem, resolved

`starbridge → gateway forward-auth (webauth decide, required_cap = vat:<id> from the route) → reverse-proxy → the vat's node endpoint (ServerRecord.endpoint)`. The vat's data plane speaks the EXACT `/status, /api/cells, /api/receipts, /api/events/stream, /turns/submit` contract, so `model/mod.rs` and every reflection/feed already work unchanged.

Today `NodeClient` has ONE credential slot (the node-operator bearer, writes only). The attach needs the **gateway credential on EVERY request** (reads + SSE + writes). Resolution, stated as design law:

- `NodeClient::Http` grows `credential: Option<String>` — attached as `Authorization: Bearer dga1_…` on all requests, including the SSE reader (which currently builds its own bare client, `client.rs:688`, and `http_get` is a bare `reqwest::blocking::get`, `client.rs:301` — both must thread it).
- **Through the gateway, the node-operator bearer becomes infra plumbing, not a renter credential.** The provider runs the vat's node; the gateway holds the node bearer in the vat record and injects it after webauth admits. The renter's real write authority is their **ed25519 signature on the turn** — the executor verifies it, and neither gateway nor provider can forge it. So remotely, all writes go via `/turns/submit` client-signed; the operator `/turn/submit` path stays a direct-dev-node convenience. This keeps the `?cap=` downscoping worry (api.rs:30 bind-internal warning) on the gateway's side of the trust line where it already lives.

**Connect ceremony (the capability presented on connect):** attach = `GET <endpoint>/status` with the credential. `200` → attached; `403 authenticated-but-uncapped` → "genuine session, not your vat" surfaced verbatim in the live-node strip (webauth's Verdict split makes this one line of UI). Then the starbridge verifies it is *your* vat, not by trusting the URL: check the ticket's `vat_cell_id` against the vat identity on the wire (add the vat cell-id to the vat-scoped `/status` mirror — `NodeStatus` today carries only `public_key`), and verify the receipt chain head against the ticket's **anchor** (`verify_receipt_chain_with_keys`, refusing `is_deferred` receipts as non-commitments). The World that follows you is one you *re-verify on arrival*, every time.

### 3. Desktop attach v0 (smallest real thing)

1. **`NodeClient.credential`** on every request + the SSE reader — ~2-3h.
2. **`--vat <ticket-uri>` arg** beside `--node` (VatTicket parse; login threading identical to `node_url` today) — ~2h.
3. **The 403 story in the strip** — attach to a foreign vat id renders "authenticated, but this is not your vat" (the cross-account test made visible) — ~1h.
4. **Promote the write wire from `UnifiedBootView` into the cockpit:** generalize `client_signed_save` (`unified_boot.rs:452`) from SetField-save to `client_signed_turn(client, node_pk, clerk, actions)`; the session already holds `signing_seed` (`login.rs:335`). Then the live-node strip's cells get the same affordance surface local cells have, firing REAL verified turns on the VAT's ledger under YOUR key — ~1-2 days.
5. **Receipt verify against the ticket anchor** in the receipts inspector for remote receipts (green/red, deferred-refused) — ~3h.

Demo sentence: *"I typed `--vat dregg-vat://…@gw` on a machine I'd never used; my cells appeared, receipts streamed, I fired a turn signed with my key, and the receipt verified against my own anchor. My neighbor's ticket got a 403."*

### 4. Web attach (increment 2) — transport, not architecture

The pure split (`live_node.rs:10-38`) was built for exactly this: `SseParser` / `ReceiptFeed` / `LiveReflection` are wasm-safe today. Design:

- **Fetch transport:** a wasm `NodeClient` backend over browser fetch (reqwest's wasm fetch backend, or web-sys). **Not `EventSource`** — it cannot set an `Authorization` header; instead a streaming `fetch` whose `ReadableStream` chunks feed the SAME `SseParser`, with our own `Last-Event-ID` resume logic (which the native reader already implements — port the loop, not the parser).
- **Same-origin serving kills CORS and is thematically right:** the gateway (or the vat itself) serves the web starbridge bundle — *your computer serves its own screen*. A foreign-origin deploy needs a CORS allowlist on the gateway; name it, don't default it.
- **Boot mode:** when a VatTicket is present, the web cockpit boots into **attach mode** — no local demo world; Home = the remote census (`/api/cells` through the existing reflections), receipts live via the fetch-stream, turns client-signed in-tab (the clerk already compiles). The wasm world stays honestly ephemeral — **the REMOTE vat is the durability**, which dissolves the `session.rs` wasm-resume gate instead of fighting it: nothing durable lives in the tab, so nothing is lost when it closes except the login.
- **Custody v0:** mnemonic → seed in tab memory for the session (the existing dev-seed shape); passkey-wrapped durable custody is the named follow-up.

### 5. Honest gaps

- **The gateway vat route + `ServerRecord.endpoint` are prerequisites from the F1 trunk** — this design lands on top of DREGG-COMPUTER.md's build-order items 1-5, it does not replace them.
- **Chain-head races:** `client_signed_save` reads the receipt head then submits; two concurrent writers to one vat can cross. Single-renter vats mostly dodge it; the fix (node-side head auto-fill for client-signed turns, like the operator path's nonce auto-fill) is a node change — named, not done.
- **The cockpit's remote surface is a strip, not a Home.** v0 reflects cells + receipts; the unified Files/Apps/Services/Grains Home over the remote census is F3's slice riding this attach.
- **Anchor distribution is still the ballgame:** the ticket carries the anchor precisely so it never comes from the vat's own wire; ticket delivery (at `vat create`, over the account session) must itself be the trustworthy channel. STARK-grade `verify_history` stays the stretch.
- **Attach-wakes-the-vat ("open the lid")** — attaching to a Sleeping vat should trigger the gateway's funded-lease wake before the node wire answers — is a lovely v1, control-plane only, not in v0.
- **`MirrorCap` (remote_mirror) is not yet the enforcement on this path** — v0 scopes by the gateway's `vat:<id>` (whole-vat); folding MirrorDepth per-cell attenuation into what a shared/sub-scoped ticket grants is the follow-up that makes "show a friend one cell of my computer" real.

**Smallest attach v0, named: `VatTicket` + credentialed `NodeClient` + the gateway vat route** — desktop `--vat` attach reflecting your remote cells and live receipts, one client-signed turn landing on the vat ledger, receipt verified against your own anchor, and a 403 on your neighbor's vat. Web follows as a transport port over the already-pure core, served same-origin by your own vat.