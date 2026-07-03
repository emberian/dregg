# DEOS NIGHT SHIFT — Fable, 2026-07-03 (~3am–morning)

Branch: `fable/deos-night-shift` (this worktree). Nothing pushed anywhere public.
Forge ritual: commit here → `git push hbox fable/deos-night-shift:refs/heads/fable/hbox-sync -f`
→ `ssh hbox 'git -C ~/dev/fable-night-shift merge --ff-only fable/hbox-sync'`
→ check/test on hbox (24 cores), logs in hbox:/tmp/fable-*.log. **No local builds** (fan discipline).

## Shipped tonight (committed, compiles green, tested on hbox)

1. **THE AGENT ROOM** (`starbridge-v2/src/deos_desktop/agent_room.rs` + wiring) — the desktop's
   first agent-as-inhabitant surface: tabs Actions (receipted turns, REFUSED in amber) ·
   Mandate (held cap edges) · Reach (CAN/CANNOT verbs), resident picker ranked by
   executor-counted nonce, default = busiest non-operator cell. Spotter + desktop menu
   reachable, own sentinel window cell (0xA6…), bake hooks, unit test green.
2. **THE PULSE** (`mod.rs::pump_dynamics` + spawn in `new()`) — 250ms dynamics-cursor pump:
   when the World moves without the desktop's hand (bot/agent/node), the icon census
   refreshes, every surface repaints off the live ledger, and foreign residents' turns are
   announced on the status bar. No refresh buttons.
3. Worktree path-dep fix: `.claude/worktrees/plonky3-recursion` symlink → `~/dev/plonky3-recursion`.

## The 13-scout fleet harvest (ultracode, ~1.7M tokens, all 13 returned)

Full structured returns (proposals with file:line anchors + step plans) live in:
- Wave 1 (desktop): `~/.claude/projects/-Users-ember-dev-breadstuffs--claude-worktrees-deos-night-shift/bc17f60d-c3bd-4fc5-8f19-b53c15b497d6/subagents/workflows/wf_32fe966d-c4b/journal.jsonl`
- Wave 2 (all other organs): same path, `wf_5a5bf69d-db3/journal.jsonl`
(one `{"type":"result",...}` line per scout; also `cv workflow <session> <run-id>` for the tree.)

Frontiers: xanadu-docuverse · daily-driver · truth-surfaces · widget-kit · inhabitation ·
performance (wave 1) — portable-IR · zed-fork · comms/matrix · agent-runtime/hermes · web ·
mobile/graphideOS · app-ecosystem (wave 2). ~70 proposals, wow 5–10.

## Real bugs the scouts found (fix regardless of any feature)

- **Spotter cannot be dismissed** — no Escape, no click-away (mod.rs spotter_dispatch region).
- **`actuate()` drops `CommitOutcome::Rejected`'s reason** — refusals vanish silently (mod.rs ~1393–1508).
- **`holds()` is `balance >= 0`** — a placeholder misreporting ocap authority in every menu (mod.rs ~1000).
- **`bake_doc_links` back-leg re-scans the same doc** — the backlink assertion never tests the real reverse scan (mod.rs ~3053).
- **`DesktopLayout::save` pretty-serializes ALL doc prose synchronously on every drag-end** (layout.rs 165–172).
- **agent.rs `build_actions` sorts every REFUSED row to the top** — interleaving with committed turns lost (agent.rs 204–248).
- **Theme inversion**: `apply_deos_theme(None,false,cx)` under OS dark mode installs cockpit GitHub-dark on the NT desktop inputs (main.rs 1025–1047).
- deos-view `BindingRegistry`/`on_committed_turn` have **zero production call sites** — shipped World-Status binds paint frozen seed values forever.
- SystemUiCapChrome runs a **private ledger** — hand-over receipts never reach the desktop World (android-cell permgate.rs ~739).
- deos-hermes `HermesSession::run` still uses **MockHermesPeer keyword scripts** in the cockpit surface (cockpit_surface.rs 146–149).

## The overnight slate (chosen for wow-per-effort · low collision · one coherent story: "the desktop woke up")

| # | item | lane | status |
|---|------|------|--------|
| 1 | Keyboard spine (⌘K Spotter, Escape ladder, arrows) + Spotter-dismiss fix | me, mod.rs core | in progress |
| 2 | REFUSED is a moment (surface refusal reasons; pairs with Agent Room) | me, mod.rs actuate | queued |
| 3 | GOSSAMER — visible transclusion threads between windows | agent, threads.rs + render tail | launching |
| 4 | BACKLINK HALO — "← quoted by N" beads, walkable | agent, halo.rs + backlinks_of extraction | launching |
| 5 | Pulse toasts (foreign turns as clickable NT cards) | me, after 3 merges (render-tail contention) | queued |
| 6 | Status bar → receipt console flyout | stretch | queued |

Morning demo script: open desktop → ⌘K, type "agent" → Agent Room (watch the treasury act;
REFUSED rows in amber) → drag a cell onto a document → **a cyan thread snaps between the
windows** → select the source → backlink beads on the halo → click a bead → walk the link
back. Meanwhile the status bar narrates every foreign turn. Zero refresh buttons anywhere.

## Big-ticket ideas parked for ember's daylight judgment (from the harvest)

- **The Rewind Rail** (10w) — scrub the whole desktop through root-verified history.
- **THE HIRELING / The Resident** (10w×2) — a real hermes brain living in the Agent Room,
  hire/fire from the desktop (needs the MockHermesPeer→real-peer weld).
- **The live Android tile** (10w) — confined app frames painted in AndroidCell windows.
- **Rehydrate & Drive over Matrix** (10w) — membrane-over-Matrix in the shipped desktop.
- **Exchange Floor** (9w) — compute-exchange × execution-lease as the $DREGG agent-economy demo.
- **App Shelf** (9w) — the 24 starbridge-apps as first-class desktop citizens.
- **Web transclusion embeds** (9w) — transclude.js + the missing /transclusion/ page.
- Zed fork: Receipt Rail (8w) then hash-linked blame (9w) — heavy build coupling, week-scale.

## Session-continuity notes (if this session ends)

- 5:15am alarm armed (Monitor). X-spaces crib sheet still TODO (task 5) — source material:
  `~/dev/collected-writings/dreggnet-tweets.md` (the full @DreggNet archive captured tonight).
- The `the-coin.txt` honest-tokenomics poster draft sits in `~/src/dregg-posters/` awaiting
  ember's red pen (lock % discrepancy 6.7 vs 6.2 must be resolved by ember before posting).
- Memory index updated at `~/.claude/projects/-Users-ember/memory/`.
