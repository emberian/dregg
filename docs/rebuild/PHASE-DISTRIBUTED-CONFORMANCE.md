# PHASE — Distributed-Layer Conformance (Lean abstraction ⇄ Rust impl)

> **Provenance.** 2026-05-31, read-only research agent (Claude Opus 4.8, 1M).
> Scope: do the REAL dregg1 Rust crates (`blocklace/`, `captp/`, `dfa/`) actually
> *implement the guarantees* the dregg2 Lean abstractions ASSUME — and which
> distributed-layer gaps block the **swap of the core** (the single-cell turn
> executor) versus only the cross-cell / multi-party extension?
> **No `.lean`/`.rs` file was edited. No build was run.** This doc is the only
> artifact.
>
> **Verdict in one line:** the Rust impls *conform in shape* to the Lean
> abstractions on the run-algebra facts (blocklace causal order, DFA accepting-run
> delivery), but each carries **one load-bearing discipline the Lean proof states
> as a hypothesis and the Rust does not check**: blocklace's content-independent
> incomparable-pair detection is narrowed to a `(creator, seq, content)` heuristic;
> CapTP's `handoff_non_amplifying` is **assumed, not enforced** by `validate_handoff`.
> **None of these gaps gate the CORE swap** — the choreography deadlock-freedom OPEN
> is *off* the single-cell critical path entirely (and is, in fact, no longer a bare
> `sorry`). They gate the **cross-cell / federation extension**. There is **zero
> Lean⇄Rust conformance harness for the distributed layer** today (the FFI golden-oracle
> cascade covers only the scalar/record *kernel*), and that — not any single
> theorem — is the highest-leverage risk.

---

## 1. Conformance table — Lean abstraction ⇄ Rust impl

| # | Lean abstraction (`file`) | Guarantee | Rust crate (`file:line`) | Conformance check exists? | Gap |
|---|---|---|---|---|---|
| B1 | `Blocklace.equivocation_detectable` / `Equivocation` (`Dregg2/Authority/Blocklace.lean:158,198`) | A fork = a pair of **incomparable** (`a∥b`, content-independent) same-author blocks; its *presence* is the proof. | `finality.rs::detect_equivocation` (`blocklace/src/finality.rs:795`) | Rust unit test `test_equivocating_block_excluded` (`ordering.rs:971`) — **NOT** against the Lean def | **NARROWER detector.** Rust keys on `creator == ∧ seq == ∧ id ≠` (`:798`); Lean keys on `creator == ∧ a∥b` (incomparable under `≺`). Two same-author blocks at *different* seq that are concurrent (an honest tip-race or a re-numbered fork) are an `Equivocation` in Lean but **not** caught by `detect_equivocation`. The paper's (and Lean's) detector is `has_equivocation_in_past` (`ordering.rs:120`, which groups by *round* and flags `len>1`) — that one IS closer to the Lean `seesBoth`/`observer_detects` shape, but it is used only inside leader-ratification, not at `receive_block`. |
| B2 | `Blocklace.Canonical` — content-address determines block; `lookup_of_mem` (`Blocklace.lean:100,106`) | The `id` is injective: no two distinct in-lace blocks share an `id`. | `BlockId(blake3(signing_content ‖ signature))` (`finality.rs:337`); `HashMap<BlockId, Block>` keyed insert (`:606,659`) | No explicit invariant test; relies on `HashMap` key uniqueness + blake3 | **CONFORMS (modulo §8).** The keyed `HashMap` *structurally* gives `Canonical` exactly as the Lean docstring says (`:96`); blake3 collision-resistance is the §8 seam, correctly NOT a Lean theorem. The one wrinkle: Lean's `Canonical` is over the abstract `id`; Rust's `id()` also hashes the *signature*, so two equally-signed-but-different-sig blocks differ in id — fine, strictly finer than Lean assumes. |
| B3 | `Blocklace.precedes` (`≺` = transitive closure of `pointed`) (`Blocklace.lean:132`) | Causal/observe order = transitive ack reachability. | `causal_past` (BFS over `predecessors`) + `is_predecessor` (`finality.rs:825,852`) | No test vs Lean | **CONFORMS.** BFS transitive-closure over `predecessors` IS `precedes`; `is_predecessor(a,b) = causal_past(b).contains(a)` matches `precedes B a b` (with the `a≠b` guard at `:853`). |
| B4 | `Blocklace.honest_no_equivocation` / `HonestChain` (`Blocklace.lean:228,238`) | An author who always acks its own tip is `≺`-totally-ordered ⇒ never an equivocator. | `add_block` makes new block point at `self.tips` (`finality.rs:638–649`, tip-update discipline) | No test vs Lean | **CONFORMS in shape.** `receive_block`/tip-update only advances the tip on higher `seq` and removes the tip for known equivocators (`:627,638,707`), realizing the single-ack-chain discipline `HonestChain` abstracts. Honesty is a *discipline of the local creator*, not enforced on received blocks — exactly as Lean models it (a hypothesis, not a checked invariant). |
| B5 | `Blocklace.attested` / `attested_mono` (`Blocklace.lean:372,380`) | Quorum (`½(n+f)`) of distinct authors ack ⇒ finality, monotone. | `FinalityTracker.record_ack` + `FinalityLevel` lattice (`finality.rs:167,655`); `Attested` once 2f+1 distinct acks | `FinalityLevel` is `Ord` + "never regresses" (doc `:166`) | **CONFORMS.** Rust `FinalityLevel::Attested` at 2f+1 distinct acks = Lean `attested` at `cfg.threshold`; the monotone-`Ord` enum realizes `attested_mono`. (The *liveness* of reaching Attested is the O2 GST OPEN of `PHASE-DISTRIBUTED-ADVERSARY.md`, not a conformance gap.) |
| C1 | `CapTP.handoff_non_amplifying` / `HandoffValid.nonAmplifying` (`Dregg2/Exec/CapTP.lean:253,295`) | Granted cap rights `≤` introducer's *held* rights (`confers held granted`). | `validate_handoff` (`captp/src/handoff.rs:374`); `SwissTable::export` (`sturdy.rs:88`) | Rust handoff unit tests (`handoff.rs:428+`) check sig/trust/expiry — **NOT** non-amplification | **ASSUMED, NOT ENFORCED.** `validate_handoff` checks introducer-sig, recipient-sig, trusted-introducer, expiry, swiss-enliven (`:383–410`) and then copies `cert.permissions` through verbatim (`:419`). There is **no** check that `cert.permissions ≤` the introducer's own rights. `SwissTable::export` (`sturdy.rs:88`) lets the introducer register *any* `AuthRequired` for a cell. So Lean's load-bearing `nonAmplifying` premise is a **trusted-introducer assumption**, not a runtime gate. |
| C2 | `CapTP.handoff_is_introduce` / Granovetter `connected` (`CapTP.lean:248,276`) | 3-vat introduction: A reaches B, A holds target, target consents — only connectivity begets connectivity. | `HandoffCertificate` flow (`handoff.rs:106–164`); swiss pre-registration at target (`:139`) | sig/trust tests only | **PARTIAL.** The *connectivity* premise (A must be able to deliver the cert to B; A pre-registered the swiss at the target) is realized structurally. But Lean's `connected : G.has introducer recipient` and `holds_target : G introducer held` are **graph facts the Rust never materializes** — there is no capability-graph object in `captp/` against which "A actually holds this" is checked; the swiss entry is self-asserted. Same root cause as C1. |
| C3 | `CapTP.handoff_forwarder_revocable` / `phi_drops_confinement` (`CapTP.lean:341,356`) | The handed-off cross-vat cap is a **revocable forwarder**: target vat can revoke by ceasing to honor the witness; permission survives, authority does not. | `SwissTable` expiry / `enliven` use-count (`sturdy.rs:159`, `EnlivenError::Expired/ExhaustedUses`); routing token issued per-validate (`handoff.rs:413`) | expiry/exhaustion unit tests (`sturdy.rs:239,264`) | **CONFORMS.** Swiss expiry + max-uses + fresh per-validate routing token IS the revocable-forwarder mechanism: the target stops honoring → the crossed cap fails to admit. Matches `ForwardedRevocable` faithfully. |
| C4 | `CapTP.pipelining_preserves_seam` (`CapTP.lean:131`) | Resolving a promise delivers the queued call but does **not** discharge its authorization. | `pipeline.rs::resolve_promise` drains queued `PipelinedMessage`s, each carrying `PipelinedAction.authorization` | (none vs Lean) | **CONFORMS in shape** — `resolve_promise` returns the queued message *with* its `authorization` for the executor to re-check; it does not run the auth. The Lean theorem is `Iff.rfl` (delivery only rewrites `targetCell`), so the conformance burden is "the executor re-validates `authorization` after delivery" — a property of the *executor*, not `pipeline.rs`; **unverified-by-test** that the executor actually does. |
| C5 | `CapTP §4` distributed-GC liveness (`CapTP.lean:405`, an `-- OPEN:`) | Eventual reclamation of unreachable exported caps. | `captp/src/gc.rs` (23 KB) | — | **HONEST OPEN both sides.** Lean leaves it a documented `-- OPEN:` (not a `sorry`); `gc.rs` is refcount + lease-timeout, which is exactly the "death is timed-out, never decided" resolution `OPEN-PROBLEMS.md` adjacent-residual #1 mandates. No conformance obligation — both sides agree it's lease-based. |
| D1 | `DfaRouting.routed_message_followed_accepting_route` (delivery soundness) (`Dregg2/Exec/DfaRouting.lean:139`) | No delivery except along a run ending in an accepting state (`last_accept?` gate). | `Router::classify_inner` (`dfa/src/router.rs`, the `let (accept_state, _) = last_accept?;` gate; `next == DEAD_STATE → break`) | Rust router tests; Lean has fail-closed `Reference` section | **CONFORMS — the cleanest of the four.** The Lean `Delivery.routes` proof-obligation IS `classify_inner`'s `last_accept?` early-return: no accepting state reached ⇒ `None` ⇒ `Unrouted` ⇒ no delivery. DEAD_STATE-breaks-walk = `δ` partiality. |
| D2 | `DfaRouting.unique_route` (determinism / no-misroute) (`DfaRouting.lean:184`) | Functional `δ` ⇒ a message has a unique route/destination. | flat `transitions[state*256+byte]` table (`router.rs`, single `StateId` per cell) | router tests | **CONFORMS.** The flat single-`StateId`-per-cell table IS `Deterministic` (`δ` functional in `(node,hop)`). |
| D3 | `DfaRouting.route_authorization` (verify-seam respect) (`DfaRouting.lean:267`) | Cannot route past an unauthorized hop; `GovernedRouter` installs tables behind a governance proof. | `GovernedRouter::update_routes` (`router.rs:669,726`) | router governance tests | **CONFORMS at table-install granularity; PER-HOP guard is Lean-only.** Rust gates *table installation* on a governance proof; the Lean `GuardedDelivery`'s per-hop `RouteAuthorized` is a finer obligation the Rust router does not implement hop-by-hop (it composes with slot caveats elsewhere, per the `dfa/src/lib.rs` "Composition notes"). Finer in Lean, coarser in Rust — not a soundness divergence, a granularity gap. |

---

## 2. THE choreography deadlock-freedom OPEN — does it gate the CORE swap?

**Sharp verdict: NO. It does not gate the swap of the single-cell turn executor.
And it is no longer the bare `sorry` the brief assumed.**

Two findings, both load-bearing.

### 2a. The theorem is PROVED (over reachable configs, on the `NoRec` fragment) — not stated-not-proved.

The brief's premise ("`deadlock_free_of_projectable` is STATED-NOT-PROVED") is
**out of date**. `Dregg2/Coordination.lean:816` carries
`deadlock_freedom_by_design` as a **genuine theorem** with a real body and
`#assert_axioms deadlock_freedom_by_design` (`:912`, sorry-free). The honest
history is right there in the file:

- The *old* statement — progress over the **initial** projections — was found
  **FALSE** and is recorded as a kernel-checked counterexample
  `deadlock_initial_counterexample` (`:765`): a `Projectable`/`NoSelfComm`/`NoRec`
  `G` with a `waiting` role whose `Dual` partner lives only in a *reachable*
  residual, not the initial config.
- The theorem was then **restated over `GReach`-reachable configurations** (the
  operationally-correct Carbone–Montesi progress shape) and **proved** for the
  recursion-free, well-scoped fragment (`NoRec` ∧ `NoSelfComm`), with the
  preservation lemmas (`GStep.noRec_preserved`, `GReach.noSelf_preserved`, …) and
  an enabled-step form `deadlock_freedom_progress_step` (`:888`).

So what *remains* open is narrow and explicitly scoped: (i) the **recursive**
fragment (`mu`/`var`) needs an unfolding `GStep`; (ii) the headline
`projection_sound` is proved only in its **head-duality** content, with the full
bisimulation left as a documented residue (`:415`); (iii) the genuinely
research-grade objects are `OPEN-PROBLEMS.md` #1 (projection-time I-confluent
split over Byzantine parties), #2 (cross-group atomic commit `[IMPOSSIBLE]`),
#3 (atomic N-ary step). None of those is `deadlock_freedom` itself.

### 2b. The single-cell turn executor does not touch `Coordination` at all.

This is the decisive structural argument. Trace the dependency cone of the
**core**:

- The core swap is, per `SUCCESSOR-ROADMAP.md:35–46`, the `turn`/`cell` crates →
  the verified kernel (`Exec.exec` / `recKExec`), whose conservation + authority +
  fail-closed are proved and **already FFI-cascaded** (`dregg-lean-ffi`,
  `differential.rs` / `state_differential.rs`). `coord` is listed as a **separate**
  REPLACE-BY-LEAN crate, not part of the kernel.
- `Coordination.lean` sits at the **top** of the stack
  (`Coordination.lean:1–11`): `CellProgram → JointTurn → Coordination`. It
  *imports* `Boundary` and `Confluence`; nothing in the single-cell turn path
  imports *it*. A `JointTurn` is one atomic step; a choreography is "a cell
  coordinating cells" — strictly a composition built **on top of** the cell, "no
  new top-level primitive" (`:30`).
- Deadlock-freedom is a **liveness/progress** property of a *multi-party,
  multi-round* protocol. A single-cell turn is a *single* atomic admissibility
  check + state transition. It has no peer to deadlock against. The MPST progress
  theorem is vacuous at arity 1.

**Therefore:** the choreography deadlock-freedom OPEN (and #1/#2/#3) gates the
**cross-cell / multi-party coordination extension** (the `coord` crate, the
federation/JointTurn-graph layer), and is **off the critical path** for swapping
the single-cell turn executor. The core swap needs only: the kernel laws
(proved), the per-cell admissibility (proved in `Boundary`/`Core`), and the
finality monotonicity over `World` (proved). It does **not** need any choreography
progress theorem.

**The one honest caveat to "off the critical path":** I-confluence
(`OPEN-PROBLEMS.md` #1/#7) is *adjacent* to the core in one specific way — a cell
that declares itself tier-1 (`FinalityRule::admits`) is making an I-confluence
claim, and `#7` records that this side-condition is **documented but not
type-checked in code**. That is a *cell-creation* gate, not a *turn-executor*
gate: a wrongly-tier-1 cell is a soundness bug in the cross-group story, but the
single-cell executor still runs its turn correctly. So even the I-confluence
residue lands on the *extension*, not the core swap — but it is the closest the
coordination layer's opens come to the core, and worth naming.

---

## 3. Conformance gaps ranked: block the CORE swap vs block the extension

### Tier 0 — Blocks the CORE swap
**(none.)**

The single-cell turn executor's Lean laws are proved and already cascaded to Rust
through the FFI golden oracle. No distributed-layer conformance gap sits on its
path. This is the genuinely good news and should be stated plainly.

### Tier 1 — Blocks the cross-cell / federation EXTENSION (soundness-relevant)

1. **C1 — CapTP non-amplification is assumed, not enforced** (`handoff.rs:419`,
   `sturdy.rs:88`). The Lean `handoff_non_amplifying` keystone rests on
   `HandoffValid.nonAmplifying`, a premise `validate_handoff` never checks. For
   the *extension* (caps crossing vats), this is the load-bearing
   only-connectivity-begets-connectivity guarantee, currently a trusted-introducer
   assumption. **Highest-severity extension gap.**
2. **B1 — blocklace equivocation detector is narrower than the Lean/paper def**
   (`finality.rs:798` vs `Blocklace.lean:158`). `detect_equivocation` is a
   `(creator,seq,id≠)` heuristic; the Lean (paper Def 4.2) detector is the
   content-independent incomparable pair. The *observer-side* `approved_by` /
   `has_equivocation_in_past` (`finality.rs:881`, `ordering.rs:120`) is the
   conformant one but is used only in leader-ratification. For the federation
   consensus extension, the gap is: a fork that re-numbers `seq` evades
   `receive_block`'s detector while still being a Lean `Equivocation`.
3. **C2 — no materialized capability graph** in `captp/` (the root cause shared
   with C1). Lean's `connected`/`holds_target` graph facts have no Rust referent;
   the swiss entry is self-asserted.

### Tier 2 — Granularity / coverage gaps (not soundness divergences)

4. **D3 — per-hop route authorization is Lean-only** (`DfaRouting.lean:267` vs
   table-install gate `router.rs:726`). Finer in Lean; composed elsewhere in Rust.
5. **C4 — pipelining seam re-check is the executor's job, untested** (the Lean
   `Iff.rfl` pushes the obligation onto the post-delivery executor).
6. **The choreography opens (#1/#2/#3) + recursive-fragment deadlock-freedom** —
   research-grade, gate the *full* multi-party story, explicitly off the core
   path (§2).

### Tier 3 — Honest OPENs, agreed on both sides (no action)

7. **C5 — distributed-GC liveness** (`gc.rs` lease-based ↔ Lean `-- OPEN:`).
8. **O2 GST-liveness** of blocklace `Attested` (handled as an assumed `World` law
   in `PHASE-DISTRIBUTED-ADVERSARY.md`).

---

## 4. Where Lean⇄Rust conformance tests / golden vectors most reduce risk

The single biggest finding: **the FFI golden-oracle cascade
(`dregg-lean-ffi`) covers ONLY the scalar kernel (`exec`) and the record-cell
kernel (`recKExec`)** — `differential.rs` / `state_differential.rs`. There is
**no** differential harness for *any* distributed-layer abstraction. The
distributed Lean theorems and the Rust crates were written against the *same prose
spec* (the docstrings cite `finality.rs:181`, `router.rs:512`, `apply.rs:2835`)
but were never mechanically cross-checked. That prose-only linkage is the risk.

Ranked by risk-reduction per unit effort:

1. **CapTP non-amplification golden vectors (closes C1, the top extension gap).**
   Generate `(held_rights, granted_rights)` pairs; assert the Lean
   `confers held granted` decision (run the Lean `HandoffValid` constructor / a
   `#eval`-able `confers` over a concrete `Rights` lattice) **equals** a Rust
   `validate_handoff`-side check — *which forces the Rust check to be written*. The
   test failing today (because Rust doesn't check it) is the point: it converts the
   trusted-introducer assumption into a fail-closed gate. Highest leverage.
2. **Blocklace equivocation differential (closes B1).** Drive random
   same-author block pairs (incl. *different-seq concurrent* forks) through the
   Lean `Equivocation`/`equivocation_detectable` (#eval-able, `Blocklace.lean:475`
   demo proves it fires) and through Rust `detect_equivocation` + `approved_by`.
   The divergence on the re-numbered-fork case *is* the conformance report; it
   tells you to route `receive_block` through the observer-side detector.
3. **A blocklace `BlockId` / `Canonical` round-trip vector** — assert the Rust
   `Block::id()` is injective on a corpus of structurally-distinct blocks and that
   the `HashMap`-keyed insert realizes Lean `Canonical` (cheap, guards B2's §8 seam
   empirically the way `state_differential` guards the JSON grammar).
4. **DFA routing golden traces (cheap, B/D already conform — regression guard).**
   Feed the Lean `Reference.goodRoute`/`badRoute` (`DfaRouting.lean:364,396`) as
   golden inputs to `Router::classify_inner`; assert delivery iff Lean
   `IsAcceptingRun`. Low risk-reduction (already conformant) but a cheap
   regression fence for the cleanest-conforming component.

The pattern to copy is exactly `state_differential.rs`'s: a small canonical wire
grammar both sides agree on, random inputs, assert agreement, divergence aborts.
"Agreement is the migration certificate" — extend that sentence from the kernel to
the distributed layer.

---

## 5. Smallest first verifiable increment

**Add a CapTP non-amplification differential to `dregg-lean-ffi`, over the
one-point→two-point `Rights` lattice, and let it fail.**

Concretely:
- Lean side: `@[export]` a `dregg_handoff_non_amplifying(held : Rights, granted : Rights) : u8`
  wrapping the decidable `confers held granted` for a small concrete `Rights`
  (the `Unit` and a 2-element lattice already used in `CapTP.lean`'s NonVacuity
  `demoCert`/`demoValid`, `:460,475`).
- Rust side: a `validate_handoff`-adjacent reference that *attempts* the same
  bound, plus the random driver.
- The harness asserts agreement; **today it diverges** (Rust has no such check),
  and that divergence is the precise, machine-checked statement of gap C1.

Why this first: (a) it is the *highest-severity extension gap* (§3 Tier-1 #1);
(b) it reuses the **existing, working** FFI cascade infrastructure (no new TCB
beyond a one-line wire grammar — two `Rights` tags); (c) it is the only gap whose
fix is a *missing check* rather than a *narrowed algorithm* (B1) or a *missing data
structure* (C2), so it is the cheapest to both detect and close; (d) it does NOT
touch the frozen dregg1 crates beyond reading them, matching the `dregg-lean-ffi`
"additive and detached" discipline. The day it goes green, the CapTP handoff is
the first distributed-layer abstraction with a real Lean⇄Rust conformance
certificate — the same status the kernel already enjoys.

---

## 6. Bottom line

- **The core swap is unblocked by the distributed layer.** The single-cell turn
  executor's laws are proved and FFI-cascaded; no blocklace/CapTP/DFA conformance
  gap and no choreography OPEN sits on its path (§2, §3 Tier-0 = empty).
- **The choreography deadlock-freedom theorem is PROVED** (reachable-config form,
  `NoRec` fragment, sorry-free; `Coordination.lean:816,912`) — the brief's
  "stated-not-proved" premise is stale. The remaining coordination opens
  (#1/#2/#3, recursive fragment, full bisimulation) gate the **multi-party
  extension**, not the core.
- **Each distributed abstraction conforms in *shape* but carries one unchecked
  discipline:** blocklace's incomparable-pair detection is narrowed to a
  `(creator,seq)` heuristic (B1); CapTP non-amplification is a trusted-introducer
  assumption, not a runtime gate (C1, the top extension gap); DFA routing is the
  cleanest, conforming on delivery-soundness and determinism (D1/D2).
- **The real risk is structural, not theorem-level:** there is **no Lean⇄Rust
  conformance harness for the distributed layer**, only for the kernel. The
  highest-leverage move is to extend the existing FFI golden-oracle cascade to the
  distributed abstractions, starting with the CapTP non-amplification differential
  — which both *is* the smallest increment and *closes the top extension gap by
  forcing the missing check to be written*.

---

### Appendix — exact citations used

- Lean abstractions: `Dregg2/Authority/Blocklace.lean:100,132,158,198,228,238,372,380,475`;
  `Dregg2/Exec/CapTP.lean:131,248,253,276,295,341,356,405`;
  `Dregg2/Exec/DfaRouting.lean:139,184,267,364,396`;
  `Dregg2/Coordination.lean:415,765,816,888,912`.
- Rust impls: `blocklace/src/finality.rs:16,130,337,345,602,624,795,825,852,881`;
  `blocklace/src/ordering.rs:120,971`;
  `captp/src/handoff.rs:106,374,413,419`; `captp/src/sturdy.rs:88,159`;
  `captp/src/gc.rs`; `captp/src/pipeline.rs` (`resolve_promise`);
  `dfa/src/router.rs` (`classify_inner`, `update_routes:726`, flat transition table).
- Cascade infra (kernel-only today): `dregg-lean-ffi/README.md`,
  `dregg-lean-ffi/src/differential.rs`, `dregg-lean-ffi/src/state_differential.rs`.
- Cross-doc: `docs/rebuild/OPEN-PROBLEMS.md` #1/#2/#3/#7 + adjacent-residual #1;
  `docs/rebuild/PHASE-DISTRIBUTED-ADVERSARY.md` (O2 GST-liveness as assumed `World`
  law); `docs/rebuild/SUCCESSOR-ROADMAP.md:29,35–46` (core = `turn`/`cell`,
  `coord` separate, consensus/finality a distinct phase).
