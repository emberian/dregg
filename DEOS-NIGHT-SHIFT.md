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
