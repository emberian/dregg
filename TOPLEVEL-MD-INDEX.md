# TOPLEVEL-MD-INDEX — canonical map of workspace-root markdown

**Date:** 2026-05-24. **Purpose:** one-stop index of every `.md` at the
workspace root, plus what was moved into `audits/` and `docs-history/`
during this audit pass. New design docs added at the toplevel should
be listed here.

Categories:

- **entry** — start here if you're new
- **canonical** — current shape-of-the-world; trust these
- **design-active** — committed direction, implementation in flight or
  imminent
- **design-study** — design exploration not yet committed; may be
  partial / contested
- **infra** — operational notes (build, machines, etc.)

Anything labelled **superseded** lives under `docs-history/` and is
preserved for archaeology, not as current truth.

---

## Toplevel `.md` (33 files)

| File | Class | One-line description |
|---|---|---|
| `README.md` | entry | Repo entry point; one-screen pitch + key capabilities. |
| `NEW-WORLD.md` | canonical | The current coherent story of what pyana is — layers, naming, composition. Read after `README.md`. |
| `PYANA_DESIGN.md` | canonical | Older architectural overview (Fabric / Cells / Turns). Pre-dates `NEW-WORLD.md`; still accurate at the headline level. |
| `BOUNDARIES.md` | canonical | What's inside, what's outside, what enforces the boundary. Companion audit set: `audits/AUDIT-privacy.md`, `audits/AUDIT-distributed-semantics.md`, `audits/AUDIT-protocol-composition.md`, `audits/AUDIT-federation.md`. |
| `PREDICATE-INVENTORY.md` | canonical | Every predicate in pyana + the `WitnessedPredicate` unification. |
| `EFFECT-VM-SHAPE-A.md` | canonical | Origin master plan for codebase remediation. Stage 3 complete; Stage 7+ work has spawned its own design docs. Updated status header points at current canonical references. |
| `EXECUTOR-HONESTY-AUDIT.md` | canonical | Framework + threat ledger for executor honesty (T1..T9+). Tracks which threats are closed at AIR, recursion, or off-chain. |
| `CAVEAT-LAYER-COVERAGE.md` | canonical | Three-layer audit (slot caveats × token caveats × Effect-VM AIRs) of constraint vocabulary coverage. |
| `STARBRIDGE-APPS-PLAN.md` | design-active | Plan for `starbridge-apps/` as the post-`apps/` userspace. Implementation underway (`starbridge-apps/nameservice`, `starbridge-apps/identity`, `starbridge-apps/subscription` already exist). |
| `STUDIO-REFACTOR-PICKUP.md` | design-active | Hand-off doc to the studio agent on returning. |
| `SILVER-VISION-E2E-VERIFICATION.md` | design-active | Cross-federation end-to-end verification design (bearer cap demo lineage). |
| `VK-AS-RE-EXECUTION-RECIPE.md` | design-active | Pre-recursion VKs commit canonical bytes — canonical encoders implemented; starbridge-apps migrated. |
| `STORAGE-AS-CELL-PROGRAMS.md` | design-active | Every storage primitive expressed as a cell-program pattern. |
| `SLOT-CAVEATS-DESIGN.md` | design-active | Lift `QueueConstraint` into `StateConstraint` so slots can host transition-aware caveats. |
| `SLOT-CAVEATS-EVALUATION.md` | design-active | Critique / evaluation of the SLOT-CAVEATS lift. |
| `AUTHORIZATION-CUSTOM-DESIGN.md` | design-active | `Authorization::Custom` proposal — `WitnessedPredicate`-based authorization modes. |
| `FEDERATION-UNIFICATION-DESIGN.md` | design-active | Collapse the four disjoint "federation" concepts into one canonical type. |
| `DFA-RATIONALIZATION-DESIGN.md` | design-active | Decide the future shape of the three DFA / pattern-routing implementations. |
| `SOVEREIGN-WITNESS-AIR-DESIGN.md` | design-active | Implementation design for the algebraic teeth identified in `audits/AUDIT-sovereign-witness-teeth.md`. |
| `STAGE-7-GAMMA-2-PI-DESIGN.md` | design-active | Bilateral cross-cell algebraic binding via shared PIs (Phase 1). Phase 1 implemented; supersedes `docs-history/STAGE-7-PLUS-DESIGN.md` and `docs-history/STAGE-7-GAMMA-AGGREGATION-DESIGN.md`. |
| `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md` | design-study | Sketch for Phase 2 (joint aggregation AIR) — picks up after the Phase 1 PI binding lands. |
| `PICKLES-OUTER-LAYER-PLAN.md` | design-study | Plan for Kimchi/Pickles as the outer recursive layer. |
| `KIMCHI-SURVEY.md` | design-study | Inventory + decision input on Kimchi-vs-Plonky3 recursion. |
| `DESIGN-dsl.md` | design-active | Pyana user-facing DSL surface. Supersedes the ad-hoc surface audited in `audits/AUDIT-dsl.md`. |
| `DESIGN-receipts.md` | design-active | Sovereign / federation / bridge receipt formats; BLS ThresholdQC; IBC-style bridge phases. |
| `DESIGN-commitment-framework.md` | design-active | Typed `Commitment<T>` framework, dual BLAKE3+Poseidon2. |
| `DESIGN-captp-integration.md` | design-active | Wire `captp/` into the AIR variants (`ExportSturdyRef` / `EnlivenRef` / `DropRef` / `ValidateHandoff`). |
| `DESIGN-pipelined-send.md` | design-active | `Effect::PipelinedSend` semantics, runtime, and AIR. |
| `DESIGN-max-custom-effects.md` | design-active | `MAX_CUSTOM_EFFECTS` constraints, costs, per-cell-program design. |
| `PERSVATI.md` | infra | Remote build offload box on the LAN. |
| `TOPLEVEL-MD-INDEX.md` | entry | This file. |

---

## `audits/` (30 files moved 2026-05-24)

Per-crate and cross-cutting audits. Keep as historical record + active
remediation pointers. Move source: workspace root.

```
audits/AUDIT-blocklace-consensus.md         audits/AUDIT-cell.md
audits/AUDIT-circuit.md                     audits/AUDIT-coord-crate.md
audits/AUDIT-CRATE-DISPOSITION.md           audits/AUDIT-distributed-semantics.md
audits/AUDIT-dsl.md                         audits/AUDIT-extension.md
audits/AUDIT-federation.md                  audits/AUDIT-intent-crate.md
audits/AUDIT-morpheus-federation-blocklace.md
audits/AUDIT-morpheus-federation-blocklace-phase3a.md
audits/AUDIT-node.md                        audits/AUDIT-nullifiers.md
audits/AUDIT-offline-mode.md                audits/AUDIT-privacy.md
audits/AUDIT-protocol-composition.md        audits/AUDIT-sdk-rest.md
audits/AUDIT-sovereign-witness-teeth.md     audits/AUDIT-trace-crate.md
audits/AUDIT-turn-executor.md               audits/AUDIT-cclerk.md
audits/AUDIT-wasm.md                        audits/BACKWATER-CRATES-AUDIT.md
audits/CELL-CRATE-REVIEW.md                 audits/MCP-AUDIT.md
audits/REVIEW-effect-vm.md                  audits/SDK-PYANASCRIPT-AUDIT.md
audits/SDK-REVIEW.md                        audits/STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md
```

---

## `docs-history/` (10 files moved 2026-05-24)

Session-snapshot, executed-plan, and superseded-design docs. Preserved
for archaeology — not current truth.

| File | Why archived |
|---|---|
| `docs-history/THOUGHTS-AND-DREAMS.md` | Session-state snapshot before context compaction. |
| `docs-history/APPS-AS-USERSPACE-AUDIT.md` | Subsumed by `STARBRIDGE-APPS-PLAN.md` + slot-caveats work. |
| `docs-history/APPS-USERSPACE-GAPS.md` | Lane-C-era gap analysis; subsumed. |
| `docs-history/DSL-TO-EFFECT-VM-FEASIBILITY-STUDY.md` | Verdict was "fool's errand"; preserved as the negative result. |
| `docs-history/PYANA-FLAWS-FROM-APPS.md` | Motivating audit; flaws either fixed, in flight, or rolled into `EXECUTOR-HONESTY-AUDIT.md`. |
| `docs-history/STAGE-7-PLUS-DESIGN.md` | Superseded by `STAGE-7-GAMMA-2-PI-DESIGN.md`. |
| `docs-history/STAGE-7-GAMMA-AGGREGATION-DESIGN.md` | Superseded by `STAGE-7-GAMMA-2-PI-DESIGN.md` (which picks γ off the shelf with Phase 1 PI binding). |
| `docs-history/WITNESSED-RECEIPT-CHAIN-DESIGN.md` | Subsumed by the current witnessed-receipt implementation + `NEW-WORLD.md`. |
| `docs-history/STAGE-3-AIR-PLAN.md` | Marked `STATUS: COMPLETE (2026-05-24)` in its own header. |
| `docs-history/DELETED-VERIFICATION-CRATE.md` | One-shot retirement note for the now-deleted `verification/` crate. |

---

## Suggested reading order for a fresh agent

1. `README.md`
2. `NEW-WORLD.md`
3. `BOUNDARIES.md`
4. `PREDICATE-INVENTORY.md`
5. `EXECUTOR-HONESTY-AUDIT.md`
6. Then jump into whichever design-active doc matches your lane.

For "what is broken right now," start in `audits/` with the crate
matching your lane, then `audits/AUDIT-protocol-composition.md` for
cross-cutting seams.
