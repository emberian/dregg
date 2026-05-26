# TOPLEVEL-MD-INDEX — canonical map of workspace-root markdown

**Date:** 2026-05-25 (updated; original: 2026-05-24). **Purpose:** one-stop
index of every `.md` at the workspace root, plus what was moved into
`audits/` and `docs-history/` during this audit pass. New design docs
added at the toplevel should be listed here.

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

## Toplevel `.md` (57 files)

### Foundational / entry

| File | Class | One-line description |
|---|---|---|
| `README.md` | entry | Repo entry point; one-screen pitch + key capabilities. |
| `NEW-WORLD.md` | canonical | The current coherent story of what dregg is — layers, naming, composition. Read after `README.md`. Updated 2026-05-25. |
| `TOPLEVEL-MD-INDEX.md` | entry | This file. Updated 2026-05-25. |

### Canonical reference

| File | Class | One-line description |
|---|---|---|
| `BOUNDARIES.md` | canonical | What's inside, what's outside, what enforces the boundary. Companion audit set: `audits/AUDIT-privacy.md`, etc. |
| `PREDICATE-INVENTORY.md` | canonical | Every predicate in dregg + the `WitnessedPredicate` unification. |
| `EFFECT-VM-SHAPE-A.md` | canonical | Origin master plan for codebase remediation. Stage 3 complete; Stage 7+ has its own docs. |
| `EXECUTOR-HONESTY-AUDIT.md` | canonical | Framework + threat ledger for executor honesty (T1..T15). Tracks which threats are closed at AIR, recursion, or off-chain. |
| `CAVEAT-LAYER-COVERAGE.md` | canonical | Three-layer audit (slot caveats × token caveats × Effect-VM AIRs) of constraint vocabulary coverage. |
| `SILVER-DEBT.md` | canonical | Per-item debt ledger (Tier 1/2/3) mapping every place the implementation falls short of the docs/tagline. §0 lists items retired this session. Added 2026-05-25. |

### Design (active)

| File | Class | One-line description |
|---|---|---|
| `STARBRIDGE-APPS-PLAN.md` | design-active | Plan for `starbridge-apps/` as the post-`apps/` userspace. |
| `STUDIO-REFACTOR-PICKUP.md` | design-active | Hand-off doc to the studio agent on returning. |
| `VK-AS-RE-EXECUTION-RECIPE.md` | design-active | Pre-recursion VKs commit canonical bytes — canonical encoders implemented; starbridge-apps migrated. |
| `STORAGE-AS-CELL-PROGRAMS.md` | design-active | Every storage primitive expressed as a cell-program pattern. |
| `SLOT-CAVEATS-DESIGN.md` | design-active | Lift `QueueConstraint` into `StateConstraint` so slots can host transition-aware caveats. |
| `SLOT-CAVEATS-EVALUATION.md` | design-active | Critique / evaluation of the SLOT-CAVEATS lift. |
| `AUTHORIZATION-CUSTOM-DESIGN.md` | design-active | `Authorization::Custom` proposal — `WitnessedPredicate`-based authorization modes. |
| `FEDERATION-UNIFICATION-DESIGN.md` | design-active | Collapse the four disjoint "federation" concepts into one canonical type. |
| `DFA-RATIONALIZATION-DESIGN.md` | design-active | Decide the future shape of the three DFA / pattern-routing implementations. |
| `SOVEREIGN-WITNESS-AIR-DESIGN.md` | design-active | Implementation design for the algebraic teeth identified in `audits/AUDIT-sovereign-witness-teeth.md`. |
| `STAGE-7-GAMMA-2-PI-DESIGN.md` | design-active | Bilateral cross-cell algebraic binding via shared PIs (Phase 1). Phase 1 implemented. |
| `DESIGN-dsl.md` | design-active | `dregg` user-facing DSL surface. |
| `DESIGN-receipts.md` | design-active | Sovereign / federation / bridge receipt formats; BLS ThresholdQC; IBC-style bridge phases. |
| `DESIGN-commitment-framework.md` | design-active | Typed `Commitment<T>` framework, dual BLAKE3+Poseidon2. |
| `DESIGN-pipelined-send.md` | design-active | `Effect::PipelinedSend` semantics, runtime, and AIR. |
| `DESIGN-max-custom-effects.md` | design-active | `MAX_CUSTOM_EFFECTS` constraints, costs, per-cell-program design. |
| `PROOF-TO-ACTION-BINDING-SWEEP.md` | design-active | Sweep of proof-to-action binding gaps across executor boundary. Added 2026-05-25. |
| `BLOCK1-BIND-CLOSURE-NOTES.md` | design-active | Closure notes for the block1-bind TODO wave (queue, capability, handoff AIR arms). Added 2026-05-25. |

### Design (study / sketch)

| File | Class | One-line description |
|---|---|---|
| `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md` | design-study | Sketch for Phase 2 (joint aggregation AIR). |
| `PICKLES-OUTER-LAYER-PLAN.md` | design-study | Plan for Kimchi/Pickles as the outer recursive layer. |
| `KIMCHI-SURVEY.md` | design-study | Inventory + decision input on Kimchi-vs-Plonky3 recursion. |
| `FEDERATION-AS-CELL.md` | design-study | Adjunction between Federation and Cell; argument for keeping them separate. |
| `EFFECT-VM-SHAPE-A.md` | design-study | (See canonical above; also serves as the original shape-A motivation doc.) |
| `CROSS-CELL-CATEGORICAL-ANALYSIS.md` | design-study | Categorical analysis of cross-cell interaction primitives. Added 2026-05-25. |
| `CROSS-CELL-COORDINATION.md` | design-study | Cross-cell coordination patterns and design tradeoffs. Added 2026-05-25. |

### Audit + study docs (session 2026-05-25)

| File | Class | One-line description |
|---|---|---|
| `AIR-SOUNDNESS-AUDIT.md` | canonical | Complete AIR soundness sweep; attack sketches for T1.5, T2.5, T2.7, T2.9, T2.11. Source commit `ce1e2def`. |
| `EXECUTOR-VK-AUDIT.md` | canonical | Executor + VK layering audit with closure plans for T1.3, T1.6, T1.7, T2.17, T2.18, T3.3. |
| `RECEIPT-ARCHITECTURE-STUDY.md` | canonical | Receipt chain / audit trail deep dive; receipts as the primary causal record. |
| `HOUYHNHNM-COMPARISON.md` | design-study | Side-by-side comparison of dregg vs. Houyhnhnm system principles. |
| `HOUYHNHNM-DEEP-CRITIQUE.md` | design-study | Deep critique of dregg from the Houyhnhnm perspective (source `1a8299eb`). |
| `PROTOCOL-CATEGORICAL-ANALYSIS.md` | design-study | Categorical treatment of dregg protocol primitives (Tier 1/2/3 punch list). |
| `TEST-REALITY-AUDIT.md` | canonical | Test suite honesty audit — fake assertions, scaffold `must_pass` labeling. |
| `DEMO-INTERACTION-MATRIX.md` | design-study | Demo scenario matrix for the two-AI handoff and related demos. |
| `STORAGE-SECONDARIES-TRIAGE.md` | design-active | Triage of storage secondary index and secondary-cell design gaps. |
| `CELL-TURN-TEST-AUDIT.md` | canonical | Per-crate test audit for cell + turn layers; new integration test inventory. |
| `CIRCUIT-VERIFIER-TEST-AUDIT.md` | canonical | Test audit for circuit + verifier layers. |
| `INTENT-BRIDGE-TEST-AUDIT.md` | canonical | Test audit for intent + bridge layers (40 tests). |
| `FEDERATION-CAPTP-TEST-AUDIT.md` | canonical | Test audit for federation + CapTP layers. |
| `SDK-NODE-WIRE-TEST-AUDIT.md` | canonical | Test audit for SDK, node, and wire layers. |
| `META-TEST-AUDIT.md` | canonical | Meta-level test audit: scaffold labels, fake assertions, must_pass demotion. |
| `SUBSTRATE-TEST-AUDIT.md` | canonical | Test audit for storage-templates, credentials, app-framework substrate. |
| `AUDIT-dregg-turn-verifier-test-quality.md` | canonical | Turn + verifier test quality audit (standalone). |

### Session summaries

| File | Class | One-line description |
|---|---|---|
| `SESSION-2026-05-25-SUMMARY.md` | entry | One-page summary of the 2026-05-25 session: soundness emergency, receipt fixes, lifecycle effects, ~200 tests, 20+ audit docs. |

### Infra

| File | Class | One-line description |
|---|---|---|
| `PERSVATI.md` | infra | Remote build offload box on the LAN. |

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
audits/REVIEW-effect-vm.md                  audits/SDK-DREGGSCRIPT-AUDIT.md
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
| `docs-history/DREGG-FLAWS-FROM-APPS.md` | Motivating audit; flaws either fixed, in flight, or rolled into `EXECUTOR-HONESTY-AUDIT.md`. |
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
