# dregg2 (Dragon's Egg) — rebuild entry point

> **Start here.** This is the navigational handoff for `docs/rebuild/`. Read the
> CANONICAL docs in the order below; everything else is rationale or grounding.
> When markdown and code disagree, **trust the code** (`file:line` citations are
> the receipts). Tags used throughout: `[G]` grounded-in-paper · `[C]`
> grounded-in-code · `[F]` forward-design · `[T]` theorizing.

## What dregg2 is, in one paragraph

dregg2 = **Robigalia**: *seL4's capability discipline extended across an untrusted
global network* — a **persistent distributed operating system** for collaborating
on untrusted code without getting hacked, where checkpoint / restore / replay /
time-travel / debugging are native consequences of the design rather than bolt-ons.
seL4 proves a machine-checked integrity theorem resting on **one trusted kernel**
mediating every invocation; dregg2 **deletes the single kernel** and spreads the
same authority structure across mutually-distrustful hosts via content-addressing,
gossip, and proofs. The architecture is one object with three faithful projections
composed at OS-scale — the **C-spine ⊕ B-law ⊕ A-style** composition: **C** = the
authority **spine** (the capability-derivation-tree, content-addressed and gossiped);
**B** = the trust **law** (soundness-by-verification — the TCB is the *verifier*, never
the solver); **A** = the soundness **style + runtime character** (a cell is live
*codata*, an element of the final coalgebra `νF`; soundness is a `▶`-guarded
bisimulation; the runtime affordances are theorems). The load-bearing honesty: across
the net **permission survives the crossing, authority does not** (Miller's
de-jure/`BA`-vs-de-facto/`TP` split) — the cross-net structure can prove a *legal
derivation existed*, not what a holder can eventually *cause*.

## Canonical reading order

| # | Doc | Status | Purpose (1 line) |
|---|---|---|---|
| 1 | `dregg2.md` | **CANONICAL** | THE consolidated architecture: the C⊕B⊕A composition, the judgements, CellProgram, cross-cell ⊗, GC, privacy, multiagent/zkRPC, proof architecture, build sequence. |
| 2 | `dregg2-multicell-privacy.md` | **CANONICAL** | The **JointTurn** (multi-cell equalizer = Mina's account-update forest), the three privacy tiers, the anti-brick upgrade clause, and the session-typed **coordination layer**. |
| 3 | `00-synthesis.md` | **CANONICAL** | The synthesis that fed `dregg2.md`: the categorical skeleton, the universal gate + await family, the pluggable finality menu, keep/diverge/recover tables. Read after `dregg2.md` for the derivation. |
| — | `GLOSSARY.md` | reference | Precise definitions of every load-bearing term. Keep open while reading. |
| — | `ROADMAP.md` | how-to-build | (sibling agent writes it) the implementation sequence from here. |

### SUPERSEDED / historical — read only for rationale
These are the explorations that **fed `dregg2.md`**; they are *not* the current design.

| Doc | What it is |
|---|---|
| `cand-A-vat-coalgebra.md` | Candidate A — the coinductive vat-coalgebra OS (→ `dregg2.md §1.3, §6, §8`). |
| `cand-B-witness-pca.md` | Candidate B — the proof-carrying turn / verifier-as-TCB (→ `§1.2, §7`). |
| `cand-C-cap-distributed.md` | Candidate C — the distributed CDT, seL4-across-the-net, LossyMorphism (→ `§1.1, §3`). |
| `01-spine-capability.md` | Spine exploration: capability-as-spine. |
| `02-spine-cell.md` | Spine exploration: cell-as-universal-object. |
| `03-spine-proof.md` | Spine exploration: proof-is-truth. |

> dregg2 is *not a winner among candidates* — it **composes** them: the three spines
> each shed the same two laws, and the three candidates are three projections of one
> generator driven to OS-scale (`dregg2.md §1.4`).

### STUDIES / grounding — the receipts behind specific claims

| Doc | Grounds |
|---|---|
| `study-gc.md` | distributed capability GC (`dregg2.md §1.7`) — incl. the acyclic-CDT vs cyclic-liveness distinction. |
| `study-consensus.md` | where consensus enters (finality tiers, I-confluence, revocation seam). |
| `study-category.md` | stress-test of the categorical model — incl. *`νF₁⊗νF₂` is NOT final*. |
| `study-mina-relink.md` | the JointTurn ≡ Mina `Zkapp_command` forest precedent. |
| `study-choreography.md` | the coordination layer + the **three orthogonal judgements** correction. |
| `gaps-1-substrate.md`, `gaps-2-distributed.md` | real Rust codebase vs the dregg2 design (CAPTURED / PARTIAL / MISSING). |

> Cross-cutting research distilled in `pdfs/discoveries.md` (the 7-agent PDF swarm) and
> `pdfs/decisions.md` (the ZK recursion/PCS rollup). The canonical docs cite both heavily.

## The executable semantics — `metatheory/`

`metatheory/` is the Lean4 (`leanprover/lean4:v4.30.0`) spec — every theorem stated
day-1 with a `sorry` body ("spec-first, grind up," mirroring l4v). It is the executable
statement of the semantics, not yet a proof.

- `Metatheory/Core.lean` — symmetric-monoidal cells/turns + the `Σ_k` conservation hom.
- `Metatheory/Laws.lean` — `Predicate ⊣ Witness` Galois connection + the verify/find seam.
- `Metatheory/Authority/Positional.lean` — the l4v integrity lift = the vat-boundary law; `LossyMorphism`.
- `Metatheory/Boundary.lean` — the DECIDED coinductive A-style soundness module: `TurnCoalg`, `Sound`/`IsBisim`, `sound_of_step_complete`, `BoundaryRespecting`.

**Crypto-soundness is NEVER merged into the Lean law** — `Verify P w` is treated as a
decidable oracle; its binding/extractability is a *circuit* obligation discharged
separately. The Lean↔Rust bridge is backend #8 of `dregg-dsl-differential` (golden
oracle, empirical cross-validation over `sorry`'d regions — not certification).

## How to implement from here

The soundness-critical first move is **NOT recursion** — it is making the per-turn
proof **step-complete** (`StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`,
all four in-circuit). Recursion is a deferrable feature behind a `RecursionBackend`
trait. See **`ROADMAP.md`** (sibling) for the ordered build sequence; the canonical
source is `dregg2.md §9` + `pdfs/decisions.md §7`.
