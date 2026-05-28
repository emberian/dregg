# apps/ Retirement Sweep — 2026-05-25

## Summary

8 app crates deleted. 3 stub directories (lending, orderbook, stablecoin) retained as CLAUDIT.md-only tombstones (no Cargo.toml, not in workspace — already cleaned in commit "retire slop apps" 2026-05-24).

---

## Retired (deleted, removed from workspace members)

| App | Crate name | LOC (Rust) | starbridge-apps counterpart | Notes |
|-----|------------|------------|-----------------------------|-------|
| apps/bounty-board | dregg-bounty-board | 3865 | none | CLAUDIT verdict: BROKEN. No payment ever moved; worker_commitment not bound; no STARK enforcement; dual divergent handler sets. |
| apps/compute-exchange | compute-exchange | 3985 | none | CLAUDIT verdict: BROKEN. Optimistic settlement discarded; dispute resolution never implemented; finalize_settlement ignores failed escrow release. |
| apps/gallery | dregg-gallery | 8489 | none | CLAUDIT verdict: BROKEN. Atomic settlement, NFT ownership, ZK proofs all decorative; Vickrey/Dutch modes unwired. |
| apps/privacy-voting | dregg-privacy-voting | 1934 | none | CLAUDIT verdict: BROKEN. Authority deanonymizes every vote at submit time; voter_pk+commitment correlated in same handler. |
| apps/identity | dregg-identity | 3083 | starbridge-apps/identity | CLAUDIT verdict: BROKEN (fails open at every trust boundary despite using real DSL circuits). Superseded. |
| apps/governed-namespace | governed-namespace | 3759 | starbridge-apps/governed-namespace | CLAUDIT verdict: BROKEN. In-memory hex-keyed naming server; dregg:// strings are opaque labels only. Superseded. |
| apps/nameservice | dregg-nameservice | 3191 | starbridge-apps/nameservice | CLAUDIT verdict: BROKEN. Superseded. |
| apps/subscription | dregg-subscription | 2927 | starbridge-apps/subscription | CLAUDIT verdict: BROKEN (healthiest of batch — real delegation verification — but still incomplete). Superseded. |

**Total Rust LOC removed: ~31,233**

---

## Retained (CLAUDIT.md tombstones only, no Cargo.toml, not in workspace)

| App | Why kept |
|-----|----------|
| apps/lending/ | CLAUDIT.md audit history only; already cleaned in prior commit. |
| apps/orderbook/ | CLAUDIT.md audit history only; already cleaned in prior commit. |
| apps/stablecoin/ | CLAUDIT.md audit history only; already cleaned in prior commit. |

These are inert directories with no source files. No action needed.

---

## Blocked on deps

None. All 8 deleted crates had zero downstream `Cargo.toml` dependents (`grep -rln` confirmed no external references to any of the crate names).

---

## Surprises

- **bounty-board** and **compute-exchange** have no `starbridge-apps/` counterparts. They are design-exploration shapeforms (per `apps/README.md`). No migration needed; they have no production path.
- **gallery** and **privacy-voting** similarly have no starbridge-apps counterparts. Same status.
- `apps/config.json` (devnet API key) and `apps/DESIGN_NOTES.md` / `apps/README.md` are retained as flat files (no crate, no workspace membership). These are documentation artifacts.
- **governed-namespace** had no CLAUDIT.md at time of sweep; verdict inferred from nameservice audit and starbridge-apps supersession.

---

## Workspace members change

Removed from `Cargo.toml` members:
- `"apps/bounty-board"`
- `"apps/compute-exchange"`
- `"apps/gallery"`
- `"apps/identity"`
- `"apps/privacy-voting"`
- `"apps/governed-namespace"`
- `"apps/nameservice"`
- `"apps/subscription"`

starbridge-apps members remain: `starbridge-apps/nameservice`, `starbridge-apps/identity`, `starbridge-apps/subscription`, `starbridge-apps/governed-namespace`.
