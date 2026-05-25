# THOUGHTS AND DREAMS

Session-state snapshot before context compaction. Written 2026-05-24
~mid-day, branch `main`. Captures what we believe right now, what we're
actively wrong about, what's in flight, and what the next session needs to
pick up without rereading the whole transcript.

## Where we are right now

**Demo passes:** 11/11 PASS including WitnessedReceipt v1 scope-1 replay.
**Stage status:**
- Stage 3 (per-variant Effect VM AIR coverage) — complete (all 41 runtime variants honest)
- Stage 7-α + γ.0 — landed (Turn::hash v3, AIR PI extensions: TURN_HASH_BASE, EFFECTS_HASH_GLOBAL_BASE, ACTOR_NONCE, PREVIOUS_RECEIPT_HASH_BASE; executor projects them; bundle PI-matching verifier)
- Stage 9 — landed (executor_signature canonical-message signing, BridgeReceiptEnvelope with 4 phases + BridgePhaseLog with monotone advancement + replay protection, cross-federation integration test)
- Stage 10 — landed (storage Poseidon2 migration + typed Commitment<T> framework)
- WitnessedReceipt v1 — landed (struct + verifier replay-chain + demo)
- Storage and cod integrated into workspace; rbg/chain/chain-program stay excluded with documented rationale

**In-flight when API rate-limited (need to relaunch):**
- Stage 7 continuation: P1.C verification (verify the 4 CapTP AIR orphans are actually proving Merkle membership, not still tautological), trace-side boundary constraints binding ACTOR_NONCE + EFFECTS_HASH_GLOBAL to in-trace witness columns, WitnessedReceipt scope-2 trace capture wired through `node/src/mcp.rs::generate_effect_vm_proof`
- Stage 8 P2.E-H: auth modes documented public surface, CI grep guard against Authorization::Unchecked, delete CompoundTurn/SettlementAction + route trustless::finalize through lowering, fix apps/nameservice + apps/privacy-voting to emit real effects

## Key insights that must not be lost

### 1. "Mangrove" is fabricated. The ζ design's central citation is hallucinated.

The Stage 7-ζ folding-research agent recommended "Mangrove-style STARK-IVC by chunking" citing
"Wong-Wagner 'Folding endgame' 2024 survey." **Deep research could not verify either name.**
Treat STAGE-7-ZETA-FOLDING-RESEARCH.md as containing one fabricated reference at its
central recommendation. The structural intuition (tree-fold + chain-fold) is approximately
right; the citation isn't.

### 2. The wrap-only-the-hash-chain construction is unsound.

The ζ doc's §5.4 wrap layer — "wrapping STARK doesn't re-execute inner AIR constraints,
just verifies hash-chain consistency over leaf-proof bytes" — is *exactly* the failure
mode the deep research names: "A hash chain binds identity, order, and integrity of
bytes; it does not by itself imply that those bytes encode valid proofs under the
intended verifier." The "prover-honesty claim, not cryptographic-soundness claim"
disclaimer is doing too much work — it's the difference between sound and unsound.

### 3. The corrected architecture: recursive verifier AIR + normalize + compress tree.

What actually works (per the deep research, validated against SP1 v6 Hypercube, Stwo/SHARP,
RISC Zero):

```
inner proof bytes → canonical parser → verifier AIR that enforces accept=1
                                       (parser + Merkle paths + challenger +
                                        FRI/openings + final accept) →
                                       acceptance bit constrained to 1 →
                                       recursive compression tree →
                                       optional final wrapper for export
```

Hash chains are fine *as metadata after acceptance is enforced*. Not as the soundness
mechanism. The `plonky3_verifier_air.rs` placeholder in our existing fork is exactly
what needs to become functional.

### 4. Kimchi/Pickles is a serious option I underweighted.

We already use Kimchi in the codebase (`circuit/src/backends/kimchi*`, `gen_kimchi`).
Mina's Pickles is production-grade recursive composition over the Pasta cycle. Mina
compresses a whole chain to 22KB with ~864-byte state proofs and ~200ms verification.
**STARK inner + Kimchi/Pickles outer** (RISC-Zero-shape but Kimchi instead of Groth16)
might be the most pragmatic path. Loses transparency-all-the-way-down; gains a
production-proven recursive layer. Should be on the table when we revisit
the corrected aggregation architecture.

The honest framing: Mina's done the recursive layer; we can use it. The cost is a
curve-substrate dependency for the outer layer only. The transparent inner stack
stays.

### 5. The Effect VM is *not* a fool's errand to extend — the DSL→Effect VM unification was.

DSL-TO-EFFECT-VM-FEASIBILITY-STUDY.md verdict: FE (Fool's Errand) for the strict
question of subsuming the Effect VM under pyana-dsl. **pyana-dsl is a caveat predicate
language**, descended from macaroons/biscuits. It's row-shaped, constraint-shaped,
multi-backend. Stretching it to be the Effect VM authoring layer fails on every
expressiveness axis (no aux columns, no multi-row continuity, no boundary kinds, no
PI layout). The Effect VM stays hand-written.

What's actually worth doing in the DSL surface:
- (b) Make `Effect::Custom` actually wire DSL-authored cell programs end-to-end via
  vk-hash registry (~300 LOC, zero IR changes)
- (d) Cross-backend differential testing (~1000 LOC, test-crate only) — emit the same
  constraint via all 7 DSL backends, run all 7 verifiers, assert agreement

### 6. The two-language model for app authoring.

pyana needs TWO surface languages at different layers:
- **pyana-dsl** (exists): caveat predicate language. Sparse. Stays focused on caveats.
- **pyanascript** (new, design in `pyanascript/`): behavior/protocol language for cell
  authoring, CapTP composition, app-framework primitives. Compiles down to typestate
  ActionBuilder calls + cell program declarations + CapTP wire protocols.

They compose: pyanascript invokes pyana-dsl when it needs a caveat predicate. They
don't compete.

**Discipline**: bottom-up. Imagine the runtime API pyanascript would compile to.
Implement primitives as ugly Rust method-chains in pyana-sdk first. If chains are
awkward, that awkwardness identifies the SDK gap. Macro the chains once they work.
*Then* consider the surface language.

### 7. Compile targets for pyanascript: CakeML > PureCake > Lean 4 > custom.

PureCake (~/dev/pure): HOL4-verified compiler for a lazy Haskell-subset (PureLang)
that lowers to CakeML. Verified chain to machine code is rare and impressive. But:
no shippable type classes yet, no import system, lazy semantics don't match actor-
shaped behavior cleanly. Interesting-but-speculative, year-scale integration.

CakeML (~/dev/CakeML): verified Standard-ML-shaped language with verified compiler
to native code (x86-64, ARMv8, MIPS, RISC-V). Strict semantics. C-shaped FFI via
`basis_ffi.c`. **Bonus: Candle is a verified HOL Light kernel *inside* CakeML** —
which is exactly what an svenvs-style verified-substrate story needs. Active dev
(~3900 commits/year). Most credible target. 3-9 months for a credible emitter,
+6-12 months for svenvs↔CakeML semantic bridge.

If CakeML's FFI seam can't carry three-party CapTP handoffs cleanly: fall back to
**Lean 4**, not a from-scratch custom impl.

Near-term experiment: 1-page proof-of-life — hand-write one cell behavior in CakeML,
link to CapTP via FFI, measure pain.

### 8. The Golden Vision in its truest articulation.

The user's framing: *"unstructured mesh of interactions, with EffectVM braiding
attestable causality over it."* Chains are convenient but the actual semantic is a
DAG: Bob's cap exercise depends causally on Alice's grant, which depended on Carol's
introduction (different cells' chains). Today's receipt chain linearizes one cell's
history; cross-cell aggregation compresses one turn's view; **the full vision is a
folded DAG attesting to "this is the causally-coherent history of the whole mesh up
to here."**

Deep research note: no public production system explicitly targets DAG-shaped IVC with
selective subgraph re-verification as a first-class feature. The pragmatic path
keeps the *proof composition layer* tree-shaped (recursive verifier AIR over a tree
of leaf proofs) and puts DAG semantics in the *statement layer* (Merkleized state
graphs, intent commitments). Anoma, Aztec, Penumbra all do this.

## Open design questions

### Q1. Kimchi/Pickles as the recursive layer?

Tradeoffs:
- (+) Production-proven; Mina exists and works
- (+) We already have Kimchi backend partially wired
- (+) Sidesteps the "make plonky3-recursion functional" problem
- (-) Curve substrate at the recursive layer (loses transparency)
- (-) Universal setup if using HyperKZG variant (might be avoidable)
- (-) Plonky3→Kimchi bridge engineering (a Kimchi circuit that verifies a Plonky3
  STARK isn't off-the-shelf)

vs. fixing plonky3-recursion's verifier AIR:
- (+) Stays transparent all the way
- (+) Same field, same hash, same toolchain
- (-) The verifier AIR is "non-functional placeholder" today — non-trivial work to
  make real

Need to decide. The deep research leans toward "fix the verifier AIR" but the user
correctly notes Mina/Kimchi already exists.

### Q2. The Stage 7-ζ pivot.

STAGE-7-ZETA-FOLDING-RESEARCH.md has the fabricated "Mangrove" reference and the
unsound wrap. Needs:
- Annotation at top: corrections-header naming the fabrication + soundness gap
- A new doc `STAGE-7-AGGREGATION-CORRECTED.md` with the SP1-style recursive verifier
  AIR + normalize + compress tree architecture, *including* a section on the
  Kimchi/Pickles option

### Q3. The effect_vm/ directory split.

`circuit/src/effect_vm/` exists as a partial split of the 8339-line `effect_vm.rs`.
It's confusing agents (multiple have flagged it). Decision: complete the split.
Defer dispatch until Stage 7 continuation lands (it touches the canonical file).

### Q4. P2's LegacyActionBuilder.

P2.A committed a typestate ActionBuilder *coexisting* with a `LegacyActionBuilder`
that 25+ call sites still use. Full migration is queued as task #53.

### Q5. SDK audit for pyanascript bottom-up.

Prerequisite to any pyanascript syntax work: rewrite (mentally) nameservice or
escrow as ugly Rust method chains using hypothetical `Cell::send / Cell::exercise /
Cell::attenuate_cap / Cell::on_receive` APIs. Every awkwardness is an API gap.
Queued as task #61.

## What needs to happen first thing next session

1. **Relaunch the rate-limited agents** (Stage 7 cont + Stage 8 P2.E-H cont). They
   had concrete briefs and concrete next steps; just hit Anthropic's rate limit.
2. **Annotate STAGE-7-ZETA-FOLDING-RESEARCH.md** with the corrections header.
3. **Write STAGE-7-AGGREGATION-CORRECTED.md** including the Kimchi/Pickles option
   as a serious alternative, not a footnote.
4. **Dispatch the effect_vm/ split completion** once Stage 7 cont lands.
5. **The Kimchi/Pickles decision** — investigate the existing
   `circuit/src/backends/kimchi*` to see what's already there, what would need to
   be added for STARK-verification-inside-Kimchi, estimate the lift vs. fixing
   plonky3-recursion.

## Outstanding tasks (by id)

- #43 Stage 7 CapTP runtime emitters + AIR fixes (in progress)
- #44 Stage 8 DSL phased rollout (in progress)
- #45 Stage 9 receipts overhaul (mostly done, may need polish)
- #46 Stage 10 storage Poseidon2 (done — close)
- #47 DSL backends tightening (done — close)
- #49 AIR nonce-bump invisibility (closed at PI level via Stage 7-γ.0; trace-side
  boundary was Stage 7 cont's job — incomplete due to rate limit)
- #50 AttestedRoot::is_valid (closed via 43f884eb + f3dc20ff)
- #51 effect_vm/ split (decision: complete; dispatch queued)
- #52 Golden Vision (aspirational, not actionable today)
- #53 LegacyActionBuilder migration (queued, post-slate)
- #54 app-framework/blinded_endpoint (closed by stabilization agent)
- #55 Tier 1 stabilization (done)
- #56-#59 Tier 4 design docs (all four delivered)
- #60 Stage 7-γ.2 bilateral cross-cell binding (queued; not blocked on folding
  research)
- #61 SDK audit for pyanascript (queued)

## Architectural mental model (one-page)

```
┌─────────────────────────────────────────────────────────────────┐
│ pyanascript (TBD)         — behavior / protocol / app authoring │
│   compiles down to ↓                                            │
│ typestate ActionBuilder + Cell::send / on_receive + caps        │
│   which use pyana-dsl ↑ for caveats                             │
├─────────────────────────────────────────────────────────────────┤
│ pyana-dsl                 — caveat predicates (sparse, stays)   │
├─────────────────────────────────────────────────────────────────┤
│ pyana-sdk                 — AgentWallet, turn submission        │
│ pyana-turn                — Turn, Effect, TurnReceipt,          │
│                              WitnessedReceipt, TurnExecutor     │
│ pyana-cell                — Cell, CellState, CellProgram,       │
│                              Capability                         │
│ pyana-captp               — sturdy refs, handoff certs,         │
│                              swiss tables, distributed GC       │
├─────────────────────────────────────────────────────────────────┤
│ pyana-circuit             — per-cell Effect VM AIR (105 cols    │
│                              after Stage 3+γ.0); STARK prover;  │
│                              Kimchi backend; plonky3 recursion  │
│                              (non-functional placeholder TBD)   │
│ pyana-verifier            — standalone proof verifier binary    │
├─────────────────────────────────────────────────────────────────┤
│ pyana-blocklace           — BFT consensus (THE live consensus,  │
│                              not morpheus/network simulator)    │
│ pyana-federation          — BLS threshold sigs, AttestedRoot,   │
│                              FederationReceipt, ThresholdQC     │
│ pyana-storage             — Poseidon2 typed Commitment<T>       │
│ pyana-wire                — CapTP wire layer over QUIC          │
└─────────────────────────────────────────────────────────────────┘

Recursive aggregation (Stage 7-γ.0 landed shared-PI bundle; ζ
direction TBD between SP1-style verifier AIR over plonky3-
recursion fork OR Kimchi/Pickles outer layer):

  per-cell proofs → shared-PI bundle (γ.0) → aggregation
                                           → chain compression
                                           → witnessed receipt
                                              for replay
```

## Things I want to be clearer about

- We work week-scale. The agent's "6-month" framings reflect my prompt bias, not
  reality.
- The user is an extremely capable researcher and implementer.
- The session has been productive. Stage 3 → 10 swept; design docs landed; rate
  limit is a hiccup, not a wall.
- Don't lose track of: pyanascript bottom-up discipline (audit SDK first);
  Kimchi/Pickles as serious recursive option; the unstructured-mesh framing as
  the actual Golden Vision.

## Cross-references

- `dev-philosophy/01-north-star.md` — what pyana is for
- `EFFECT-VM-SHAPE-A.md` — master Effect VM plan (mostly executed)
- `STAGE-3-AIR-PLAN.md` — Stage 3 complete record
- `STAGE-7-PLUS-DESIGN.md` — Stage 7+ design
- `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` — cross-cell binding (γ.1 subsumed by ζ)
- `STAGE-7-ZETA-FOLDING-RESEARCH.md` — **contains fabricated reference; needs
  corrections header**
- `WITNESSED-RECEIPT-CHAIN-DESIGN.md` — replay design (v1 landed)
- `DSL-TO-EFFECT-VM-FEASIBILITY-STUDY.md` — Fool's Errand verdict on
  DSL→EffectVM unification
- `pyanascript/README.md` — two-language model + bottom-up discipline
- `pyanascript/exploration-pure-and-cakeml.md` — verified-compile-target survey
- `AUDIT-morpheus-federation-blocklace.md` + `-phase3a.md` — what's dead-vs-live
- `DELETED-VERIFICATION-CRATE.md` — why the typed-composition checker got cut
