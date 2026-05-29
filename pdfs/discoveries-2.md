# Discoveries-2 — gaps found reading dregg2 + the choreography/MPST corpus

**For:** the rebuild-driving agent (author of `docs/rebuild/dregg2.md` + `ROADMAP.md`).
**What this is:** after grounding the named fetch list (MPST / Choral / CALM / coordination-avoidance /
crash-MPST / Byzantine-session-types / crypto-choreographies — all now in `pdfs/`) and reading `dregg2.md`
+ `ROADMAP.md`, here are **five gaps that weren't on anyone's fetch list**, each with the literature now
pulled, plus one **internal inconsistency** in the design worth fixing. Companion to `discoveries.md` +
`decisions.md`. Tags `[G]`/`[C]`/`[F]`.

The design is strong and mostly self-grounding; these are additive. The **#1 open problem (the
projection-time split) is now corpus-grounded** — see `STUDY-projection-split.md` (the attempt).

---

## 0. Internal inconsistency to fix first: the I-confluence judgement has no metatheory module

`dregg2 §2.3` declares **I-confluence a co-equal third judgement** (conservation ⊥ ordering ⊥
I-confluence, with `linear ⇏ I-confluent` and `I-confluent ⇏ linear` shown independent). But `§8`'s
module map is **Core (conservation) / Laws (Galois) / Authority (positional) / Boundary (coinductive)** —
**there is no Lean home for I-confluence / CRDT-merge / tier-1-eligibility.** The `§2.2` tier-1
well-formedness side-condition (`I(x) ∧ I(y) ⇒ I(x ⊔ y)` ⟹ tier-1-eligible, else static type error) is
asserted but un-modelled. **Recommend: add `Metatheory/Confluence.lean`** — the join-semilattice +
invariant-preservation judgement that classifies tier eligibility — grounded in the certified-CRDT
precedent (gap 2). Without it the "three judgements" framing is 2-in-Lean-plus-1-in-prose.

---

## 1. Cyclic distributed GC — strengthen the lease-expiry punt toward ORCA `[G]`

`§1.7` / `§10` honesty-note / Phase 4.2 correctly flag: refcount-at-zero collects the **acyclic CDT**, but
the **cyclic live-reachability graph** (A↔B) needs a mark-from-roots trace refcounting can't supply; the
design ships acyclic-only + **lease-expiry for cycles**. Pony's **ORCA** is the verified precedent that may
do better: fully-concurrent actor GC with a protocol that collects cyclic garbage *without* a global
stop-the-world, co-designed with the type system (deny capabilities). And it has a **machine-checked
soundness proof** (ESOP'18). Pulled: `orca-actor-gc-type-codesign-oopsla17`, `orca-soundness-concurrent-actor-gc-esop18`.
**Question for the study:** can ORCA's confirmation-protocol cycle-detection run over the vat/CapTP session
graph (the design's GC *is* the await/discharge backward face) under *Byzantine* (not just crash) peers, or
does Byzantine-safety force the lease-expiry fallback to stay? That Byzantine delta is the real open piece.

---

## 2. The I-confluence module's precedent: certified CRDTs / MRDTs `[G]`

For `Metatheory/Confluence.lean` (gap 0). The literature has *exactly* this, machine-checked:
- `verifying-strong-eventual-consistency-crdt-isabelle` (Gomes–Kleppmann, OOPSLA'17) — **the** certified-CRDT
  framework in Isabelle: prove SEC (commutativity + a network model) once, instantiate per data type. The
  template for stating I-confluence as a discharged Lean obligation, not a prose assertion.
- `certified-mergeable-replicated-data-types-pldi22` (Kaki/Nagar) — MRDTs with a **reduce-to-a-sequential-
  spec** verification; matches dregg's "sets → cells with a merge" move.
- `replicated-data-types-spec-verification-optimality-popl14` (Burckhardt) — the foundational spec/verification
  framework (the abstract-state/visibility-relation model I-confluence quantifies over).
- `katara-synthesizing-crdts-verified-lifting` — **synthesizes** a CRDT (the merge) from a sequential type
  with verified lifting; relevant to "given a cell's `CellProgram`, derive its tier-1 merge or prove it can't
  have one" — i.e. the *constructive* side of the tier-eligibility classifier.

---

## 3. Lean4 coinduction tooling — the `Boundary.lean` keystone blocker `[G]`

`Boundary.lean`'s `sound_of_step_complete` needs a **`▶`-guarded bisimulation** over the codata `Cell = νC.
µI. StepProof I × (Turn ⇒ C)`. But **Lean4 has no native coinductive types** as clean as Coq/Agda — this is a
concrete tooling risk for the *last, keystone* module. Pulled:
- `lean4-codatatype-package-qpf-keizer` — a **definitional (co)datatype package for Lean 4 built on QPFs
  (quotients of polynomial functors)**. This is *the* practical answer to "how do we even write `νC. µI. …`
  in Lean4." Read it before committing the `Boundary.lean` encoding.
- `guarded-dependent-type-theory-coinductive` (1601.01586) — the `▶` later-modality + clock-quantification
  theory the guard is borrowed from; tells you what `previous_receipt_hash`-as-`▶` must satisfy for
  productivity/unique-fixpoint, and where Lean4 (no native clocks) will need an explicit encoding or a
  bisimulation-up-to relation instead.
- **Likely consequence:** state soundness as an **explicit bisimulation relation** (`IsBisim`, greatest
  fixpoint via `coinduction` / `pgfp` in mathlib or hand-rolled) rather than a literal guarded type — the
  Keizer package shows the QPF route. Confirm which mathlib has.

---

## 4. Schema-DAG fork/merge migration — edit lenses / Cambria `[G]`

`§5` proves transparency for **linear-chain** migration and flags the **DAG (fork/merge) case open**. The tool
is **edit lenses**: `edit-lenses-hofmann-pierce-wagner` (the bidirectional-transformation mechanism that
propagates *edits* — not states — symmetrically), which is exactly what **Cambria** (Kleppmann/Litt, edit-lenses
for distributed schema evolution; paywalled, named) builds on. A migration over a *branching* schema history =
a lens between schema versions composed over the version-DAG; the transparency theorem generalizes to the DAG
iff the lenses satisfy the round-trip laws *and* compose along merges. Pairs with the linear-drop conservation
obligation (`§5`): a lens that drops a linear slot must emit `Σ before = Σ after + Σ dropped`.

---

## 5. Modern CALM languages — compiling the I-confluent fragment `[G]`

The design cites the **CALM theorem** (monotonicity ⟺ coordination-free) but not the **languages** built on
it. For the eventual "compile the statically-classified I-confluent fragment to a coordination-free runtime,
the rest to JointTurns" (Phase-7-adjacent / the coordination module): `hydro-compiler-for-distributed-programs`
(Hellerstein's modern CALM-based distributed-program compiler — the closest existing thing to "compile a
program split into coordination-free + coordinated fragments") + `dedalus-datalog-in-time-and-space` (the
temporal-Datalog substrate). These are the engineering precedent for the projection-split's *back end*, once
the front-end theorem (gap 6) exists.

---

## 6. The #1 open problem, now grounded — the projection-time split `[G/F]`

Not a gap in *coverage* (the corpus is now complete) but the **frontier theorem** the coordination module
needs. See `STUDY-projection-split.md` for the attempt. The marriage of three literatures that don't talk:
- **MPST endpoint projection** — `mpst-honda-yoshida-carbone-jacm`, `less-is-more-mpst-revisited` +
  `-revisited-2402.16741`, `mpst-generalising-projection`, `mpst-semantic-global-type-wellformedness`;
  failures: `mpst-crash-stop-async`, `mpst-crash-failure-typing-viering`; foundation:
  `deadlock-freedom-by-design-choreography-cm13`; LL coupling: `coherence-generalises-duality-mpst`,
  `logical-interpretation-async-mpst`, `formulas-as-processes-deadlock-freedom-choreographies`.
- **BEC invariant-confluence** — `keeping-calm-distributed-consistency`, `coordination-avoidance-bailis`,
  `interactive-checks-coordination-avoidance-vldb19` (the static I-confluence *checker* — the tooling), the
  2026 `coordination-criterion`, + `byzantine-eventual-consistency` (already in library).
- **CryptoConcurrency dynamic escalation** (already in library) + Byzantine choreographies:
  `bft-web-services-session-types`, `cryptographic-choreographies`, `security-protocols-as-choreographies`.
- Resource coupling: `move-resources-safe-abstraction-money`, `affine-rust-mpst` (affine = drop/cancel in
  Rust+MPST). Languages: `choral-`, `functional-`, `haschor-` choreographic programming.

The target object (the agent's verdict, which I endorse): **a projection-time static analysis that splits a
multiparty global type `G` into (a) a BEC-I-confluent, partition-progressing fragment and (b) a
conservation-coupled, atomic-JointTurn fragment, proven sound (endpoint behaviour ≈ `G`) over Byzantine
participants.** Open sub-problems D (atomic N-ary choreography steps) and E (partition/Byzantine
choreographies) both reduce to it.

---

## Net

The design needs **one structural fix** (add `Confluence.lean` for the third judgement — §0) and is otherwise
additively served by: ORCA for cyclic GC (§1), certified-CRDTs for the confluence module (§2), the Lean4-QPF
codatatype package for the `Boundary.lean` keystone (§3), edit-lenses for DAG-migration (§4), Hydro/Dedalus for
the I-confluent-fragment compiler (§5). The real frontier is the projection-time split (§6), now fully
corpus-grounded and attempted in `STUDY-projection-split.md`.

---

## 7. Study results (rollup of the four `STUDY-*.md`)

Four follow-on studies attacked the gaps above. They **interlock** on one reused primitive — the **CG-2 ⊗ CG-5
bilateral-aggregation binding (γ.2)** — which turns out to be the JointTurn, the projection-split's *red*
fragment, AND cyclic-GC Tier-B all at once; and the missing **`Confluence.lean`** is what the projection-split
*blue* clause and the tier-eligibility classifier both consume. Fix the one structural gap and three results
land on the same proven binding.

- **`STUDY-cyclic-gc.md`** — ORCA's "no cycle treatment" is single-owner deferred refcounting; true actor-cycles
  it punts to MAC. The decisive asymmetry: **refcount fails *safe* (leak); a cooperative cycle-collector fails
  *unsafe* under a liar** (a forged back-edge → use-after-free), and the hidden back-edge is exactly what tier-3
  graph-privacy conceals. ⇒ **trust-scoped hybrid:** Tier A local-cycle-collection inside a vat (provable, ORCA
  Lemma 2 port), Tier B ORCA/MAC confirmation inside a cooperative quorum **as a `JointTurn` over the SCC**, Tier C
  lease-expiry across Byzantine (unchanged, principled). `Live(c) := SelfReachable ∨ QuorumAttested(¬dead) ∨
  ¬LeaseLapsed`; the **lease is a `µ` clock over the `ν` codata — the dual of the `▶` guard**. Open: cross-Byzantine
  cyclic GC plausibly *reduces to the revocation consensus seam* (then lease-expiry is a theorem, not a punt).
  Prereq: the `gc.rs:14` `StrandId` re-keying.
- **`STUDY-confluence-module.md`** — designs `Metatheory/Confluence.lean` (closes §0). `IConfluent I W` over a
  `CellLattice` (mathlib `SemilatticeSup`+`OrderBot`), Bailis Def 6 with the common-ancestor `Reachable`
  restriction (the #1 risk if dropped). Independence theorems with finite witnesses (`linear_not_iconfluent`
  pool-overdraw / `iconfluent_not_linear` G-counter). Gomes–Kleppmann "prove-SEC-once" ported as Lean classes +
  a full **`StateConstraint` → I-confluent? table** (`Monotonic`/`WriteOnce`/`CapabilityUniqueness` yes;
  `Gte`/`Lte`/`SumEquals`/`BoundedBy`/`RateLimitBySum`/`BoundDelta` no). `needsConsensus := ¬tier1_ok`.
  Placement: parallel to `Laws`, depends on `Core` only; feeds `Boundary` via `requiredTier → commitTier`.
  **Updated discharge order: Core + Laws + Confluence (parallel) → Authority → Boundary.**
- **`STUDY-lean4-coinduction.md`** — the keystone needs only a **relational greatest-fixpoint**, fully first-class
  in plain Lean4 (`OrderHom.gfp`+`gfp_induction`; `MvQPF.Cofix`/`Fix` available if value-level `Cell` is ever
  needed). `▶` = `Later := id` (productivity assumed via `StepComplete` contractivity) or explicit ℕ-step-indexing.
  **Do NOT move to Coq.** Found two scaffold bugs (the keystone `sound_of_step_complete` is *currently unprovable
  as stated* — needs the golden-oracle bridge surfaced; `boundary_respecting_sound` is a one-liner) + a `sorry`-free
  proof skeleton.
- **`STUDY-projection-split.md`** — the frontier. Split rule = **Whittaker segmented invariant-confluence** (blue =
  I-confluent within a segment, partition-tolerant; red = crosses a segment boundary → atomic JointTurn), tightened
  by BEC's iff and CryptoConcurrency's dynamic N-ary escalation. **Genuinely new** (vs assembled): (1) the colouring
  as a projection-time analysis, (2) the **boundary lemma** (coupled-step output → I-confluent-step input — provable
  when session-ordered, a well-formedness restriction under shared-cell concurrency), (3) **Byzantine-EPP-by-
  verification** ("you can't type a liar"). Colouring undecidable in general, **decidable for the linear/integer
  conservation invariant**. Minimal first theorem: 3-party escrow (blue Offer/Accept/Receipt + red Settle), Settle =
  the existing `bilateral_action` JointTurn.

**The convergent verdict, now from four more angles:** the soundness-critical risk is **impl-side
step-completeness** (ROADMAP Phase 0) — not tooling, not recursion, not the prover. Everything else is additive,
buildable, and mostly reuses existing γ.2 / `program.rs` / `captp` code.
