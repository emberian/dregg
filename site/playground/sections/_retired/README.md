# Retired playground sections

These section modules were retired as part of the playground → Starbridge
migration (STARBRIDGE-PLAN.md §4.9, "Retire outright"). They are kept here for
reference only — they are no longer imported by `playground.js`, have no nav
entry, and no `#section-*` mount point in `playground/index.html`.

Each was retired because it was fictional / JS-simulated, violating the
substrate rule (§1: "Don't add JS-side reimplementations of dregg behavior").
The real platform inspectors under `site/src/_includes/studio/inspectors/`
now cover these concepts against the canonical wasm runtime.

| File | Why retired | Real replacement |
|---|---|---|
| `full-turn-proof.js` | Proof metrics were `Math.random()` — no real prover/verifier was ever invoked. | `<dregg-proof>` + `<dregg-turn-debugger>` over a real committed turn (see the Proofs and Effect VM sections, now Tier-2 embedded). |
| `crossfed.js` | Cross-federation "bridge" was pure `setTimeout` animation with no canonical bridge call. | `<dregg-federation>` + `<dregg-block-dag>` (Federation section deeplinks) and the real federation/peer-exchange flows. |
| `tiered-revocation.js` | Modeled a stale epoch-based revocation scheme that no longer matches the canonical `RevocationChannelSet`. | `<dregg-revocation-channel>` (real `create_revocation_channel` / `trip_channel` / `is_channel_active`). |

The gallery's AMM-swap tab was also retired in the same pass (it referenced a
deleted slop app and relied on conservation/composition wasm calls that now
fail closed). That code was deleted in place from `gallery.js` rather than
moved here, since it was one tab inside a still-live section.

Do not re-import these. If a concept here is worth reviving, build it as a
canonical `<dregg-*>` inspector instead.
