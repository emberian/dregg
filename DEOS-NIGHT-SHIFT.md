# DEOS NIGHT SHIFT — Fable · 2026-07-03, ~3am→dawn

Branch: `fable/deos-night-shift` (this worktree). **Full lib gauntlet: 850 passed / 0 failed.**
Forge ritual: commit → `git push hbox fable/deos-night-shift:refs/heads/fable/hbox-sync -f`
→ `ssh hbox 'git -C ~/dev/fable-night-shift merge --ff-only fable/hbox-sync'` → check/test
there (logs hbox:/tmp/fable-*.log). No local builds. Morning frame: `night-shift-woven.png`
(re-baking with the shelf + rail as `fable-woven-3.png` on hbox).

## SHIPPED & INTEGRATED (all hbox-verified, all in the woven bake's witness tour)

1. **THE AGENT ROOM** — agent-as-inhabitant window: Actions (receipts, REFUSED amber) ·
   Mandate · Reach; resident picker by executor-counted nonce. `agent_room.rs`
2. **THE PULSE** — 250ms dynamics pump; the desktop repaints when the World moves without
   its hand; foreign turns narrated on the status bar. No refresh buttons.
3. **KEYBOARD SPINE** — ⌘K/Ctrl-K Spotter, ↑/↓ clamped selection, the Escape ladder
   (spotter → menu → dialog → halo). Fixed scout-found trap: Spotter was undismissable.
4. **REFUSED IS A MOMENT** — `outcome_verdict` carries the executor's refusal reason (and
   action index) onto the glass at all four actuation sites.
5. **PULSE TOASTS** — foreign motion as NT cards (green committed / amber REFUSED),
   self-retiring, capped, click-through to the Transcript. `toasts.rs`
6. **GOSSAMER** — cyan transclusion threads between windows (Xanadu's visible connection),
   walkable endpoints, parallel-thread fanning, persisted View-menu toggle. `threads.rs`
7. **BACKLINK HALO** — "← quoted by N" witness arc + walkable beads on the halo;
   `backlinks_of` extraction (one truth, two surfaces); fixed `bake_doc_links` bug.
8. **THE APP SHELF** — the starbridge-apps registry as first-class citizens: shelf window,
   Spotter launch (`LaunchApp`), real `launch_on_world` (cell + receipt on the LIVE World),
   installed icons wear app faces. 6 real-executor tests. `app_shelf.rs` (874 lines)
9. **THE HIRELING phase 1** — `deos-hermes/src/resident.rs`: `ResidentBrain` = hermetic
   `LocalBrain` default | BYO-key `HttpLlm` (Anthropic or OpenAI-compatible, via curl;
   key never crosses the tool-call/receipt wire — the brain-pocket invariant).
   `examples/resident.rs` acceptance harness (real receipted turns + an in-band REFUSAL).
   Desktop seam: `starbridge-v2/src/resident_agent.rs::hire_resident` (mirror-weld commits
   real turns per Allow). Agent Room hire/fire buttons = next weld.
10. **THE REWIND RAIL** — scrub the whole desktop through root-verified history
    (`History::reify_to`, fail-closed, memoized). `holds()` correctly gates verbs to LIVE.
    World Explorer reads a `WorldLens` (amber REPLAYED banner). `rewind.rs` (752 lines)
11. **NT room stays LIGHT** — kit theme no longer follows OS dark mode into the desktop.
12. **Extended woven bake** — the tour now machine-witnesses ALL of the above (steps 4e–4i:
    Agent Room, GOSSAMER thread, toasts, spine, App Shelf launch, Rewind scrub).

## THE BUNDLE (ember's manifest → planner's honest table, full detail in wf_f1c82037-aff journal)

| component | state | est |
|---|---|---|
| zed IDE fork | lite pane WORKS in default build; full Zed = standalone workspace only | 2h |
| alacritty terminal | WORKS in default build (zed's alacritty_terminal grid + PTY) | 2h |
| hermes agent | gateway/confinement REAL + red-teamed; shipped pane brain was scripted — HIRELING fixes substrate; label honestly | 8h |
| matrix client | headless lib live-proven; GUI pane boots on mock sync | 6h |
| dreggnet cloud | REAL and deployed (34.224.208.52, *.dregg.works) but zero in-bundle integration | 4h |
| servo browser | WORKS on mac (libservo green e2e); SWGL fallback proven | 4h |
| gpui cell desktop | the real thing, hot (tonight); durable-image weld coded but not wired to `--desktop` (headline-claim drift risk) | 8h |

**Critical path:** freeze + per-OS feature matrix (mac full · linux full · win-x86_64 reduced
· win-arm64 sel4-thin) → the three long-pole builds start at hour 0 → honest labeling in
their shadow. **Top risks:** (1) Linux verified build has NEVER existed — hbox lacked
`libdregg_lean.a`; bootstrap now running (elan installed tonight; mathlib cache next).
(2) default features silently became an elephant (servo+mozjs). (3) installers workflow
never proven green. (4) Windows rebuild is artisanal. (8) mock-brain confusion at launch —
HIRELING + honest labels are the answer.

## Findings for daylight

- **Pre-existing cockpit stack overflow** (first-ever full-suite run found it):
  `cockpit::frame::layout_cell_drives_the_rail_and_a_reshape_moves_a_surface` overflows the
  default 2MB test stack; passes in 3.3s under `RUST_MIN_STACK=33554432`. Deep-but-finite
  recursion in the layout/reshape fold — wants an iterative rewrite, cockpit lane, not mine.
- The 13-scout harvest (~70 anchored proposals) + heavy-wave lane reports live in the
  workflow journals (`wf_32fe966d-c4b`, `wf_5a5bf69d-db3`, `wf_f1c82037-aff` under
  `~/.claude/projects/.../subagents/workflows/`). Unimplemented headliners queued:
  Exchange Floor, Matrix Rehydrate&Drive, web transclude.js, Android live tile,
  Pulse→Signals weld (deos-view staleness), receipt-console flyout, uniform_list
  virtualization, layout-save debounce.
- App Shelf honest seams: install ceremony/persistence future; 4 apps have wired live
  fires, the other ~16 launch + surface an honest refusal naming the seam.

## Also on your desk

- `~/dev/collected-writings/xspaces-crib-2026-07-04.md` — spaces crib (⚠ verify lock % 6.2
  vs 6.7 and the loaded numbers before speaking).
- `~/src/dregg-posters/the-coin.txt` — honest-tokenomics poster draft, needs your red pen.
- `~/dev/collected-writings/dreggnet-tweets.{md,jsonl}` — full @DreggNet archive.
- Memory updated: `~/.claude/projects/-Users-ember/memory/`.

## MILESTONE 2026-07-03 ~07:0x — FIRST LINUX VERIFIED RELEASE BUILD EVER
hbox: elan + scripts/bootstrap.sh green → libdregg_lean.a linked → cargo build --release
green → ./target/release/starbridge-v2 --headless: VERDICT ✓ (frames committed, two
distinct receipts, both refusals fail-closed citing the executor's reason). 415MB binary.
Bundle risk #1 retired: mac AND linux can build the verified shape. Next: linux packaging.

## MILESTONE 2026-07-03 ~05:14 — FIRST LINUX AppImage EVER BUILT
hbox: starbridge-v2/dist/starbridge-v2-linux-x86_64.AppImage (158MB) — cockpit + bundled
dregg-node (--run-node dispatcher) + the self-describing vessel (19.4MB dregg-src payload,
5.2x zstd). Assembled by the never-proven installers recipe, adapted (cockpit binary lives
in the ROOT workspace target/ on this checkout, not starbridge-v2/target/ — CI recipe
assumes the standalone workspace; noted for the workflow fix). Smoke: both binaries + the
vessel extracted and asserted. Planner risk #3 (linux leg): retired.

## WAVE 3 INTEGRATED ~06:0x — the desktop is an ECONOMY now
Pulse→Signals weld (World-Status binds finally live, dirty-glow) · Exchange Floor (offers/
leases as cells, Σδ=0 settlement, over-budget cheat refused in-band) · Agent Room HIRE/
STEP/FIRE (a real confined resident on the live World; refusals as amber toasts) — all
merged, 864 lib tests + 5 weld tests green, woven tour beats 4j/4k witness the hire and
the trade. Layout-saver perf fix in (coalescing writer thread for hot paths). The bake's
World now ends at 11 cells / 9 windows: the demo image grows a population during the tour.

## ~06:1x — receipt console + interleaving fix integrated (865 green)
say() spine: 80 status sites swept; console flyout (dark, 64-line log, unread chip);
height tray → Transcript click. agent.rs REFUSED rows now interleave in true stream order
(regression-pinned). LayoutSaver perf fix landed earlier. WAVE 4 launched
(wf_9e8fd7e1-e45): NT scrollbars everywhere · CardPane rides the pulse (+ CapRevoked/
CellMutated projection) · Spotter verbs-with-args + recent-jumps.

## ~06:5x — WAVE 4 INTEGRATED first-try (882 green + bake)
NT scrollbars on every dense face (persistent scroll positions, ScrollbarShow::Always NT
dress) · CardPane rides the pulse (bind cache + glow + own-turn watermark; CapRevoked/
CellMutated folded) · Spotter is a command line (transfer/grant/bump verbs → verified
turns; recent jumps on empty query). kind_short moved to chrome.rs. WAVE 5 next:
matrix-rehydrate · web-transclude · provenance-walker.

## ~07:2x — WAVE 5 INTEGRATED (898 green + bake)
THE MATRIX ROOM (membranes over the wire: rooms as live cells, sends as receipted turns
decoded off the receipt chain, mint→rehydrate→drive→stitch legs real, homeserver an
env-gated named seam) · TRANSCLUSION ON THE OPEN WEB (site/transclusion demo page +
embeddable transclude.js — hash-verified quotes, refusal chrome, backlinks; build tooth in
build-pages-dist.sh) · THE PROVENANCE WALKER (walk the receipt chain hash-by-hash, every
link recomputed; Broken/Unanchored/Deferred/Reseeded verdicts). Fixes en route: AppContext
import, Debug derive, reseeded_flags row-0 semantics (impl contradicted its own doc+test).
Ten waves of organs on the branch now; 898 lib tests.

## ~morning — THE CORE SESSION (ember redirected me from surfaces to foundation)
Adversarial core audit (7 lenses → find → refute → keep survivors): 21 raised, 19 confirmed
by a skeptic whose default was REFUTED. Artifact: CORE-AUDIT.md. Headline soundness cluster
(#1/#3/#4): the durable overlay's change-set is a hand-maintained syntactic effect walk
(collect_touched, ~13 of 30+ variants) instead of the executor's real journal write-set →
Mint/Burn/CreateCell/deploy_factory records the correct root but an incomplete overlay →
recovery refuses a valid image or silently truncates a committed turn. HELD for review (the
correct fix touches the verified turn crate's surface; the quick fix is the fragility that
caused it). Put to ember via AskUserQuestion — my rec: expose the journal write-set (option A).

Fixed + verified this session (933 lib tests green):
- #5 Discord toggle could never fire OFF → emits both affordances
- #7 engine-twin AddToSlot overflow (panic/wrap vs saturate) → saturating_add, both agree
- #6 dynamics forest-depth truncation (nested SetField never invalidated its bind → stale
  paint) → both loops use CallTree::iter_dfs
- SAFETY: the durable-image weld defaulted to Durable, which armed audit-#1 (the desktop
  CreateCells via App Shelf/Exchange/letters) → flipped to EPHEMERAL default, opt-in via
  --durable-world / --world-image path.

Wave 7 integrated (4 lanes): durable-image weld (opt-in) · uncap-the-world virtualization
(tail-following Chronicle/Ledger/Transcript/console via v_virtual_list) · Attach Wizard
(five-minute resident onboarding) · Letter Office (mail as cells; fixed its ocap — send/
deliver act on non-self cells, needed genesis_grant_cap, not open_permissions).

Also surfaced: deos-view integration test renders_inspector_card_to_pixels is RED on the
branch (view_source lacks "Cell State"/"inc"), regressed by an earlier deos-view wave,
invisible until now because gauntlets only ran -p starbridge-v2 --lib. Wants a deos-view lane.

## ~late morning — HAVE A DREGG COMPUTER (the coherence layer) + wave B
Ember reframed the whole thing: not "rent a vat" but "HAVE A DREGG COMPUTER" — yours, follows
you (local + web starbridge), can't be lied to, lives in the cloud. Killer app: persistent/
resumable/forkable/explorable HERMESES + a beautiful management console (not xterm). Design
wave wf_eec2e0e5-f31 (5 scouts + synthesis, 1 lane resumable) → DREGG-COMPUTER.md. HEADLINE:
the vat substrate ALREADY EXISTS as DreggNet ServerFleet/ServerRecord — persistent, durable,
per-period-metered, and fork()/wake=resume/stop=checkpoint/time-travel are ALREADY REAL. Gap
is pure wiring: auth→funded-lease→ServerFleet→per-vat cap (vat:<cell-id>)→reachable endpoint.
The unification is literal: a grain is a cell, a hermes is a cell, the vat is a cell — one cap
grammar, one witness discipline, one settlement rail. v0 slice: "rent a Dregg Computer, hold a
key that reaches only yours, see its cells, verify one receipt against your own key, restart
the provider — it followed you." ~90% assembly of pieces that work.

Wave B (audit slate + atlas) integrated, 940 starbridge + 22 deos-view green: #8 resolve_mounts
total-work budget (k^depth fan-out DoS) · #11 dynamics ring-buffer eviction + cursor-safe since()
+ conservative pump recovery · aspirational-honesty (#12/#16/#17 comments corrected) · atlas
refreshed + docs/what-is-deos.html explainer. Also: stopped checking render PNGs into git.
Demo video: no rendered file on-disk; the demo is DreggNet/demo/{run-demo.sh (Stripe→lease→
durable exec), crash-resume.sh ("on-camera crash-resume proof")} — the resume story, camera-ready.
