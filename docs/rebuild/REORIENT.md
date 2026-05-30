# REORIENT.md — the path to the Magnesium Vision (verified-dregg2)

> **Read this first.** You are picking up dregg2. This doc is the orientation a previous
> agent wishes it had had at the *start* of its session instead of re-deriving it painfully.
> It tells you (1) what the goal actually is and at what altitude, (2) what is live vs stale,
> (3) what to read, (4) where the code really is, (5) **the concrete path**, (6) the
> discipline, and (7) the traps that already burned someone. When markdown and code disagree,
> trust the code (`file:line` are receipts). The whole `docs/rebuild/` + `pdfs/` corpus is the
> thinking; the metatheory is the artifact.

---

## 0. The Vision, in one breath — "Mg Vision"

**Magnesium Vision = verified-dregg2** (the user's name; magnesium is hard and bright).
dregg2 is **Robigalia**: seL4's capability discipline extended across an untrusted global
network — a **persistent distributed OS** where developers/agents collaborate on untrusted
code without getting hacked, and where **checkpoint / restore / replay / time-travel /
debugger are native consequences (theorems), not features**. The Mg Vision is that whole
thing, **executable and verified in Lean4**.

**The one structural fact that reorganizes everything:** `./metatheory` **IS dregg2** — Lean4
is the *actual executable implementation* of the system, built l4v-shaped (Abstract Spec →
executable Design-Spec → Refinement). The Rust cascade is downstream and later (to start,
Rust just *calls* the compiled Lean — the FFI beachhead already works). **You do not go
refactor the Rust.** You grow the executable Lean dregg2 toward the full architecture.

---

## 1. STALE vs LIVE (read this before you read anything else)

- **STALE — do NOT build to these:** `00-synthesis.md §7/§9`, `ROADMAP.md`, `dregg2.md §9`
  as a *build plan*, and `DREGG1-TO-DREGG2.md` / `SUCCESSOR-ROADMAP.md`. These framed dregg2 as
  a **Rust refactor** with Lean as a side "golden oracle" (Phase-0-audit-`turn`/`circuit`,
  auth-in-proof via `schnorr_air`+`spec_eval`+EffectVM). **That plan is dead.** If you find
  yourself about to audit `turn/src/executor/` or compose the EffectVM, you have drifted into
  the stale frame. Stop.
- **LIVE — build to these:** `CLAUDETHOUGHT.md` (the vision in plain words), `cand-A-vat-coalgebra.md`
  (the living-cell center), `dregg2.md §0–§8` + `dregg2-multicell-privacy.md` (the *architecture*,
  not the §9 build sequence), `GLOSSARY.md` (every load-bearing term), and the `pdfs/`
  distillations below. The **architecture content** of the canonical docs is live; their
  *Rust-build-sequence* is stale.

---

## 2. The architecture, at altitude (hold all of this; don't reduce it)

dregg2 = **C-spine ⊕ B-law ⊕ A-style**, three faithful projections of one generator (the
*turn*), composed at OS-scale. With **D** (choreography) as the eventual front-end.

- **A (the center) — the living coinductive cell.** `Cell = νC. µI. StepProof I × (Turn ⇒ C)`,
  a point of the final coalgebra `νF, F X = Obs × (AdmissibleTurn ⇒ X)`. **The CellProgram IS
  the coalgebra structure-map** (the `AdmissibleTurn ⇒ Cell` arrow). Soundness is a **▶-guarded
  bisimulation** to a golden-oracle spec. **Checkpoint/restore/replay/time-travel are theorems**
  (anamorphism re-seeding + the rollback-handler turn). This is what makes dregg an OS and not a
  chain. *(`cand-A`, `decisions.md §2`, `STUDY-lean4-coinduction.md`.)*
- **C (the spine) — the authority CDT.** `CDT ≡ strand-log ≡ biscuit-graph` (one append-only
  content-addressed partial order). A cap is a derivation node; the **derivation proof makes
  "proof-is-truth" native** — an exercise *is* the traversal of an authorized arrow. The
  **vat-boundary** converts caps↔keys (`ρ_in`/`ρ_out`, a *named-lossy* Φ dropping confinement +
  revocable-forwarders). Honest rail: **permission survives the crossing, authority does not**
  (de-jure/`TP` vs de-facto/`BA`; truth-is-the-log). *(`cand-C`, `discoveries.md §2/§6`.)*
- **B (the law) — soundness-by-verification.** TCB = the *verifier*, never the solver. Every
  *search* (match a fill, find a delegation path, a handler, an order, "is this cell dead") is
  **undecidable** and must be an untrusted plugin emitting a checkable witness; every *gate* is
  cheap to **VERIFY**. This **verify/find seam** appeared four independent ways. The badge =
  `(permitted) ∧ (effects-committed)`, NOT a grant of standing. *(`cand-B`, `discoveries.md §1`.)*

**The load-bearing substructure** every projection rests on:
- **The step-complete turn:** `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`. The
  distinctive coinductive failure mode is the **drifting future** — a non-contractive step that
  locally type-checks while leaking `Σ_k` unboundedly. **Step-completeness, not recursion, is THE
  soundness question** (said four ways in `decisions.md`/the candidates/README). Recursion is a
  deferrable feature behind a `RecursionBackend` trait.
- **The JointTurn = Mina's account-update forest** (`study-mina-relink.md`): atomicity is a
  **proof property** (prophecy `will_succeed` + in-circuit cumulative-AND), not a live 2PC. The
  **CG-2 ⊗ CG-5 binding is an irreducible HYPOTHESIS** because `νF₁⊗νF₂` is *not* final
  (`study-category.md`) — cross-cell soundness is NOT `per-cell-sound ∧ per-cell-sound`.
- **Three orthogonal judgements** per turn (`study-choreography.md`, `study-consensus.md`):
  conservation (linear, Law 1), ordering (pluggable finality tier, Law 2), and **I-confluence**
  (BEC invariant-merge) — which is **NOT the session type** (linear ⇏ I-confluent; the live
  soundness risk is a `balance≥0` cell wrongly allowed at tier-1).
- **The camera** (Iris): conservation and authority are *one law* at the resource-algebra tier —
  `ConfinesAuthority := Fpu` (frame-preserving update). The camera is **full**, not
  ZK-restricted; the ZK-able fragment is a sub-camera.

**Honest bounds (design *around* these; do not "fix"):** cross-disjoint-group atomic commit
*blocks* under partition (the price of no global ledger); no unconditional/arbitrary-depth IVC
(depth = security parameter); distributed cycle-GC is out of scope ("dead" is not co-witnessable;
reclaim by lease-expiry); revocation has a recency floor under partition. *(`OPEN-PROBLEMS.md`.)*

---

## 3. What to read (and in what order)

**Tier 1 — get the altitude (start here):** `cand-A-vat-coalgebra.md`, `CLAUDETHOUGHT.md`,
`GLOSSARY.md`, `pdfs/decisions.md §2`, **`pdfs/STUDY-lean4-coinduction.md`** (the *how-to* for the
living cell in Lean — relational gfp, the golden-oracle bridge, why no QPF is needed),
`pdfs/discoveries.md` (the 7-agent distillation; the six corrections; the verify/find seam).

**Tier 2 — the full architecture:** `dregg2.md`, `dregg2-multicell-privacy.md`,
`pdfs/LEARNINGS-metatheory-verification.md` (the verification approach: Lean = core + golden
oracle; refinement-as-contract, not extraction; Iris only for the live-session interior).

**Tier 3 — the studies (the sharp findings):** `study-category.md` (tensor non-finality →
JointTurn binding irreducible), `study-mina-relink.md` (forest-as-atomic-commit, anti-brick),
`study-consensus.md` (consensus = canonicity not validity), `study-gc.md` (death undecidable),
`study-choreography.md` (linearity ≠ I-confluence). The four candidates + three spines are the
dialectic (`README.md` has the map). `gaps-1/2` = what dregg2 the *design* still misses
(economics, product/MCP, distributed GC, market machinery — mostly "above/sideways" the core).

**The library:** `pdfs/` has ~249 papers + ~28 distillation `.md`s (`INDEX.md`, `READING-LIST.md`
map them; `LEARNINGS-*.md` and `STUDY-*.md` are the per-cluster receipts; `PATHB-*.md` /
`DECISION-*.md` are the ZK-recursion rollup behind `decisions.md`).

---

## 4. Where the metatheory actually is (honest state)

`./metatheory/` — Lean4 v4.30.0 + mathlib (local path). ~33 modules compile. **What's real and
on-vision:**
- **The step-complete spine — PROVED and central.** `Exec/StepComplete.lean: cexec_attests`
  proves all four `StepInv` conjuncts on a *running machine* (`ChainedState`). This is the
  thing dregg1's docs say is unverified-and-probably-false in the real system — **in the Lean
  cell it is proved**. That is the whole point of building dregg2 as executable Lean.
- **The coinductive frame — present, relational.** `Boundary.lean` has `TurnCoalg`
  (`step : X → Obs × (AdmissibleTurn → X)`), `StepInv`/`StepComplete`, and `stepComplete_preserves`
  (PROVED safety-invariant). **But the genuine bisimulation keystone is missing:**
  `sound_of_step_complete` was found false-as-stated (free `Spec`, refuted via `Spec=Empty`) and
  downgraded. `STUDY-lean4-coinduction.md §3.2` shows the **stronger, real** version is recoverable
  by surfacing the golden-oracle bridge — that is the move (§5 below).
- **The camera** (`Resource.lean`: `conservation_is_fpu`, the camera tier), **the authority lift**
  (`Authority/Positional.lean`: the l4v integrity case-split = vat-boundary law), **the JointTurn**
  (`JointTurn.lean`: `binding_is_proper`, `joint_sound` given the binding), **Finality**/**Confluence**
  (the ordering + I-confluence judgements), the **CryptoKernel/World portals**, the **circuit
  bridge** (`Circuit.lean`), the working **FFI** (`dregg-lean-ffi/`). ~11–19 honest `sorry` (no
  cheats), classified into §8 crypto-interface obligations + genuine deep-open theorems.
- **The Preserves data substrate + structure-map (built last session, on-vision in SHAPE):**
  `Exec/Value.lean` (name-keyed records over a `Schema`; `flatten_width` PROVED — a schema fixes a
  wire layout) and `Exec/Program.lean` (the real `StateConstraint` catalog + `CellProgram` evaluator
  + default-deny + Heyting — faithful to `cell/src/program.rs`, name-keyed not 8-slot).

**The gap / the shadow:** `Value`/`Program` were built **flat and dead** — a `Bool` admissibility
checker disconnected from the *living* cell. `Exec/CellProgram → Boundary.TurnCoalg` is the standing
`OPEN`. The cell has no `νF` life, no bisimulation soundness, no checkpoint/replay theorems yet.
**`Exec/RecordCircuit.lean`** (a bit-decomposition ZK-over-records circuit compiler) is real and
proven but is the **§8 circuit obligation the design says to keep OUT of the semantic law** — it is
the orthogonal rib, not the spine; don't mistake it for progress on the core.

---

## 5. THE PATH — build the living coinductive cell (the next move)

This is the unification, and `STUDY-lean4-coinduction.md` shows it's *cheap* in Lean4 (relational
greatest-fixpoint; no QPF, no codata datatype; `Later = id` is fine because productivity is carried
by `StepComplete`, not the guard). Steps:

1. **Instantiate the living cell as a concrete `Boundary.TurnCoalg`.** Carrier =
   `Cell = (state : Value, program : CellProgram, caps, log : List Turn)` (extend / reuse
   `ChainedState`). `Obs` = the committed head (e.g. `hash(state, log-head)` — the badge).
   `AdmissibleTurn` = the turns the cell admits-and-commits; **`Program.admits ∘ exec` IS the
   structure-map's `step`.** This wires `Value`/`Program` into `Boundary` — the dead fragments
   become the body of a living coalgebra.
2. **Define the golden-oracle `Spec` coalgebra + the bridge** (`decode`/`h_obs`/`h_step`), per
   `STUDY-lean4-coinduction §3.2`. The spec is the Lean reference semantics (decidable, the oracle).
3. **Recover `sound_of_step_complete` as a genuine bisimulation for this cell.** Soundness = the
   running cell is behaviourally equivalent to the golden oracle *forever, given* step-completeness
   — and **`cexec_attests` already supplies that hypothesis** (all four conjuncts). The study's
   skeleton closes with no `sorry` once the oracle bridge is explicit. This is the keystone that the
   safety-invariant reframe only approximated.
4. **Derive the runtime-character theorems** over the codata: checkpoint = name a `(head, receipt)`;
   restore = re-seed the anamorphism; replay = re-run from the log; time-travel = fork the unfold.
   These are *theorems*, per `cand-A §5` — the Robigalia payoff made literal.

**Then grow (in roughly this order), keeping every law green:** wire `Authority.Integrity` at the
boundary (the vat-boundary law on the *real* cell — intra trivial / cross `Discharged P w`); make
state multi-asset via the `Resource` camera; lift the executable cross-cell turn to the `JointTurn`
tensor (the `BoundDelta` half-edges = CG-5); make `CellProgram::Circuit` route through the
CryptoKernel portal (NOT into the Lean law). The choreography front-end (`Projection`/`cand-D`) is
**last** and rests on open theorems — don't start there.

---

## 6. The discipline / rails (non-negotiable)

- **Crypto-soundness is NEVER merged into the Lean law** (the §8 caveat, in every candidate + README
  + GLOSSARY). `Verify P w : Bool` is a *decidable oracle*; its binding/extractability is a circuit
  obligation, discharged separately. The Lean cell proves "*if* Verify accepts *then* admissible";
  Rust+circuits prove "Verify accepts ⇒ it actually happened." Two obligations, never one.
- **Step-completeness is THE soundness question.** Everything downstream is conditional on it. In the
  Lean cell, make it hold *by construction* (`cexec_attests`); never weaken `StepInv` to fake it.
- **No fake-to-pass.** No `axiom`/`admit`/`native_decide`/`sorry`-aliases; never weaken a statement to
  close it. An honest `-- OPEN:`/`-- PRIMITIVE:` `sorry` beats a vacuous theorem. The swarms have
  *correctly refused* to fake over-strong claims before (and caught ~4 false-as-stated theorems);
  honor that.
- **Improve, don't degrade.** When an audit finds a gap, fix it; don't add "experimental" flags or
  downgrade a tier to reflect a known gap.
- **The differential bridge is cross-validation, not certification** over `sorry`'d regions (Lean =
  golden oracle, backend #8). Don't overclaim it.
- **Lean gotchas (re-learned, will bite you):** `/-- -/` doc-comments can't precede `mutual` (put
  them on the inner `def`); nested-`List` inductives don't auto-derive `DecidableEq` (drop or write
  manual); recursion through `List.any`/`.all`/`.map` needs explicit mutual list-helpers or
  `termination_by sizeOf`; `Finsupp` `+` is noncomputable (use `CellId → ℤ` + `Finset.sum`); `omega`
  doesn't see through abbrevs. Iterate with `lake env lean <file>` (race-free, fast) not full builds.

---

## 7. Traps the last agent fell into (so you don't)

1. **Don't get lost in stale docs.** Half a session was burned anchoring on the Rust-refactor
   build-plan (ROADMAP/synthesis §9) and proposing to audit `turn`/`circuit`. §1 above is the
   antidote — `./metatheory` IS dregg2; you grow the Lean, you don't refactor the Rust.
2. **Don't build flat fragments beside the spine.** The previous agent built `Value`/`Program`/
   `RecordCircuit` as dead, disconnected pieces and called it "the comprehensive step." It wasn't —
   it was a record-checker + a zkVM-arithmetic compiler, **the part of dregg that isn't dregg.** The
   living cell (the `νF` bisimulation, the authority spine, the JointTurn) is what makes it dregg.
   **Grow the existing coinductive modules; don't start a parallel toy.**
3. **Don't reduce dregg2 to a constraint-checker / ZK-over-records tool.** That's `RecordCircuit`,
   and it's the *explicitly-orthogonal §8 obligation*, not the semantic core. The core is the living
   capability cell whose soundness is bisimulation.
4. **Don't let "executable" drop the coinduction.** `decisions.md §2` is emphatic: state soundness
   *coinductively* (TurnCoalg, bisimulation, `▶`), not inductively over `List Turn`. The cell is a
   living process, not a fold over a transaction list.
5. **Read `pdfs/` — it's the deepest grounding.** The canonical docs cite `discoveries.md`/
   `decisions.md` on nearly every claim, and `STUDY-lean4-coinduction.md` is the literal technique
   guide for the keystone. The previous agent worked without it for too long.

---

*The egg metaphor still holds: we're figuring out what's inside without cracking it. The center is a
living, capability-secure, step-complete, bisimulation-sound cell — build that, and the OS follows.*
🐉🥚
