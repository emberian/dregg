# PHASE-SHIFT — from verified metatheory to a constructed dregg

> The Spec layer is mature and interrelated (`Dregg2.Spec.*` + `Coherence`, the actual metatheory
> in `Metatheory.*`, the honesty-CI in `Claims.lean`/`CLAIMS.md`). This doc records the phase we are
> now entering: **close the verification loop and construct the actual system** — eDSLs,
> metaprogramming, tactics, VCG/WP, the real CryptoKernel, the Rust cascade, the first verified app.
> It synthesizes five study agents (construction, eDSL, metaprogramming/tactics, VCG/WP, CryptoKernel);
> the per-study detail lives in the session transcript and can be expanded into the named `PHASE-*.md`.

---

## 0. Honest status anchor (2026-05-30)

A verified **micro-core** (`Exec/Kernel.exec` over a toy `KernelState = Finset accounts + bal:CellId→ℤ
+ caps`, conservation + fail-closed authority PROVED), a mature **abstract Spec web**
(`Spec/{Guard,Conservation,Authority,Lifecycle,Hyperedge,Choreography,Await,VatBoundary}` cross-linked
by `Coherence`), the **actual metatheory** (`Metatheory/{ConstructiveKnowledge,Categorical,EpistemicDial}`),
the **first `Exec ⊑ Spec` square** (`Spec/ExecRefinement` — conservation + authority projections
PROVED, operational LTS OPEN), a content-addressed cell substrate **built but not wired**
(`Exec/Value`), and a working **FFI beachhead** (`dregg-lean-ffi/`, 10k/10k golden-oracle differential).
This is **not** a verified distributed OS, **not yet** a dregg1 successor — a well-architected seed.

## 1. The single highest-leverage next move

**Wire `Exec/Value.lean` into `Exec/Kernel.lean`** — replace the toy `bal : CellId→ℤ` with the
content-addressed `Value` record cell-state, re-proving `exec_conserves`/`exec_authorized`/`cexec_attests`
over the `balance` field (a localized re-proof aided by `flatten_width`). It is the one move with the
largest unblocking radius: every later phase (catalog, LTS, cascade, application) needs the concrete
cell; it is the prerequisite `Value.lean` was built for but never connected to; and it turns the
10k/10k FFI differential from a scalar PoC into the real migration ratchet.

## 2. The phase sequence + critical path

```
(i) Prelude + concrete-cell instance ─┬─► (ii) catalog instantiation ─┐
   Spec/Prelude.lean ; Value→Kernel    │     (constraints/effects/auths │
   (Coherence §7 proves the merge sound)│      as DERIVED Spec ctors)     ▼
                                        └────────────────────► (iii) Exec rework = FULL Spec
                                                                     refinement (the operational LTS)
                          (iv) CryptoKernel overhaul ── parallel ───────────┤
                                                                            ▼
                                                                  (v) Rust cascade (turn/cell/coord→FFI)
                                                                            ▼
                                                                  (vi) first verified app (RDII/transfer)
```
Critical path: **(i) → (ii) → (iii) operational-LTS → (v.Cascade-2) → (vi)**. The single longest pole
is **(iii): the abstract small-step LTS / full forward-simulation diagram** (the OPEN in
`ExecRefinement §4` and `Proof/Refine`) — it is RESEARCH, not engineering, and everything downstream
depends on it. (iv) CryptoKernel + (v.Cascade-1) run in parallel and rejoin at Cascade-2.

## 3. The refinement-to-implementation strategy (partitioned by trust)

| Part | Strategy | Why |
|---|---|---|
| semantic decision core (admissible? conserves? authorized?) | **Lean-as-host (FFI)** baseline + **differential golden-oracle** ratchet | small, soundness-critical, proved — host it, diff native against it until equal, then native is certified-by-oracle |
| crypto / proving / transport / persistence | `@[extern]` **portal instances** (`CryptoKernel`/`World`), validated by differential on their *laws* | Lean never proves crypto soundness (the §8 boundary) |
| products (node/extension/cli/sdk) | **stay-Rust**, hosting the FFI-shim kernel | above the core |
| long-run | Lean→Rust **extraction** | only once a *verified* extraction exists — off the critical path; do not build now |

The "closed loop" = the three-layer tower **Metatheory ⊒ Spec ⊒ Exec ⊒ Rust**, each link a refinement
square, with §8 crypto cut out to circuits. Minimal first loop: the **RDII/transfer** (`Protocol/Workflow`)
— an authorization that is machine-checked, not asserted, from the abstract `Guard` law to the running
Rust the extension calls.

## 4. The four tooling tracks (what each must deliver)

- **eDSL** (`PHASE-EDSL`). Build **DSL-A first**: a cell-program DSL (`dregg_program { invariant {…}; on m {…} }`)
  elaborating, via `declare_syntax_cat` + `macro_rules`, onto the *existing* `RecordProgram`/`Guard`
  smart-constructors — a **parser onto already-proved constructors** (no new metatheory). It is the
  direct, in-situ-verified replacement for dregg1's external `#[dregg_caveat]`/`#[dregg_effect]` (whose
  meaning lives only in codegen). Restrict to the decidable first-party fragment first; defer the
  witnessed/proof-carrying atoms and the choreography (DSL-B) / effect (DSL-C) DSLs.
- **Metaprogramming + tactics** (`PHASE-METAPROGRAMMING`). Build first 3: **`#assert_axioms_all <ns>
  [except …]`** (collapse the 110-line `Claims.lean` ledger; pure rejector); the **`catalog … where`
  codegen** (generate the ~90 coproduct variants as smart-constructor + `admits`-characterization +
  auto-`#assert_axioms` triples — wiring the honesty tripwire into 100% of output, eliminating ~85% of
  the hand-decls); the **`discharge` tactic** + an **`aesop Dregg2` rule-set** (aesop is in the toolchain
  but unused) — the guard-seam opener every characterization/admissibility proof starts with. Then
  `refine_square`, `conserve_multi`, `attenuate`, the `verify-catalog.sh` Rust↔Lean diff. Every tactic
  keeps the `Conserve.lean` fail-loud rail (never fake-close).
- **VCG / WP** (`PHASE-VCG-WP`). A **weakest-precondition calculus** over the `Option`-monad transition
  (`wp step t Q s := ∀ s', step s t = some s' → Q s'`), Hoare triples as the surface, characteristic
  formulae reserved for the `νF` life. Conservation gets the **separation-logic / camera** treatment
  (the frame rule's soundness *is* `Fpu`/`conservation_is_fpu`; private case = same triple over the
  commitment monoid via `committed_iff_cleartext`). The key leverage: **the run-level WP-soundness is
  ALREADY proved — it is `stepComplete_preserves`/`invariant_run`**; the VCG only *generates* the
  per-turn obligations. First version: partial-correctness, single-cell, discrete-camera, run-invariant
  over the record kernel — fully supported today. Defer the step-indexed Iris `iProp` (higher-order
  recursive resource invariants — the `R ≅ R→Prop` self-reference) — it is correctly fenced in
  `StepCamera`. Worked examples: monotonic counter (closable today), escrow (single-ledger today;
  cross-vat routes conservation to the JointTurn CG-5 hypothesis).
- **CryptoKernel overhaul** (`PHASE-CRYPTOKERNEL`). Split the flat uninterpreted `CryptoKernel` into
  **three layered classes**: `CryptoPrimitives` (Poseidon2 `compress`, Pedersen `commit`+`commit_hom`,
  `nullifier` — *algebraic* laws proved, *computational* hardness as `Prop` carriers, not idealized
  `hash_inj`); **`VerifierKernel`** (whose `verify` is *defined* as "the extracted circuit is satisfiable",
  with `verify_sound` a **derived theorem** generalizing `verify_law_derivable` off the toy `kernelCircuit`
  onto a Lean `CircuitIR` mirroring the real `ConstraintExpr`); `PredicateKernel` (the 8 `WitnessedKind`s
  as per-kind `KindObligation`s — circuit + statement algebra + `Dial` floor — finally **wiring
  `EpistemicDial`** to the per-kind verifier). One trust boundary = the FRI/DLog/Poseidon-CR `Prop`
  carriers; everything above is proved. Commit to **STARK-native recursion, no folding**
  (`DECISION-recursion-strategy.md`: a hash-FRI STARK has no additively-homomorphic commitment, killing
  the Nova/ProtoStar line). **First end-to-end §8 discharge: Merkle membership** (Rust AIR already real
  and sound; Lean gadget pattern ready in `RecordCircuit.range_iff`; exercises the full
  bridge→verify_sound→registry_sound→dial cascade; needs no curve algebra) — then Pedersen conservation,
  then the rest.

## 5. Honest blockers + risks

- **RESEARCH (may not close):** the operational LTS / full forward-simulation diagram (iii) — the
  longest pole, gates the coinductive `Boundary` keystone; the three-judgement projection split
  (`OPEN-PROBLEMS #1`, no paper); cross-disjoint-group atomic+live+partition-tolerant commit
  (`[IMPOSSIBLE]` — design around it); the deep coinductive/Byzantine/GST sorrys (bucket 2).
- **HARD ENGINEERING:** the §8 discharge (real AIR over records, prover extraction); the Lean→Rust
  trust boundary at scale (marshalling `Digest`/`Proof`/`Finset` state must not become an unverified
  TCB; differential is *cross-validation, not certification*); **step-completeness in dregg1 is
  unverified and probably false today** (auth runs outside the proof in `authorize.rs`) — a Phase-0
  audit GATES Cascade-2.
- **MECHANICAL (tool-de-risked):** the `Spec/Prelude` factoring (Coherence §7 proves it sound); the
  catalog instantiation (voluminous → the codegen removes the toil); FFI past scalars.

## 6. Recommended first 90 days

1–30: factor `Spec/Prelude`; **wire `Value` into `Kernel`** (the #1 move); run the Phase-0
step-completeness audit on dregg1's `turn`/`authorize.rs` (gates the cascade — do it cheaply, now).
31–60: stand up `#assert_axioms_all` + catalog-codegen + `discharge`; generate the first catalog slice;
extend `ExecRefinement` from the toy transfer to the `Workflow` gate.
61–90: generalize the FFI past scalars (differential-gated); drive the **RDII/transfer closed loop**
end-to-end on the smallest surface; *start* the operational-LTS research as a parallel long pole.

> svenvs (vertical: verify the cage), dregg2 (horizontal: verify the web), stella (the deliberately-open
> inside) are one triangle on one realizability gate. The honesty discipline — labeled buckets, a
> build-failing claims ledger, the retraction-is-the-method — is shared across all three, and it is what
> lets "verified" mean exactly what it says and no more. 🐉🥚
