# Metatheory

Lean4 metatheory for the dregg2 vat model. Toolchain `leanprover/lean4:v4.30.0`
(matches `~/src/mathlib4`). Style: **spec-first, grind up** — every theorem is
stated on day 1 with a `sorry` body; discharge Core (category laws) and
Conservation (the monoid-hom) first, the vat-boundary law last (mirrors l4v).

## Candidate-INDEPENDENT modules (scaffolded here)

All three dregg2 candidates share the same three judgements and the same authority
model, so these are stable regardless of which candidate is chosen:

- **`Metatheory/Core.lean`** — the symmetric-monoidal category of cells (objects)
  and turns (morphisms). `Σ_k` (conservation, **judgement 1**) as a **monoid-
  homomorphism on counts + invariance on ordinary turns** (`Σ_k (A⊗B) = Σ_k A +
  Σ_k B`; `Σ_k A = Σ_k B` on every non-mint/burn hom-set — invariance `=`, not a
  monotone `≥`). The "strong monoidal functor" packaging is decorative (its target
  is discrete on objects). Mint/burn are explicit typed generators. Withholding =
  copy `Δ` / erase `◇` comonoid coherence.
- **`Metatheory/Resource.lean`** — the **resource-algebra (camera) tier** behind
  conservation. `Core` conserves a measure in any `AddCommMonoid` (multi-asset,
  fractional, debt); `Resource` handles resources whose composition is *partial /
  invalid*: `ResourceAlgebra` (Iris camera = partial CM + `valid` + `core`), `Fpu`
  (frame-preserving update — the general conservation law, of which "sum preserved" is
  the `(ℕ,+)` shadow), with the `ℕ` camera, `Fpu.refl/trans`, and NFT non-duplication
  (`excl_no_dup`) **proved** (no `sorry`), plus the `Auth` sovereign↔fragment sketch.
  At this tier the conservation law and the authority law coincide (both = FPU).
  Precedent: Jung et al., *Iris from the Ground Up* (JFP 2018); Boyland (fractions);
  Move (linear resources). **The camera is FULL, not ZK-restricted:** the
  runtime/intra-vat register (caps-as-caps) admits any camera with no circuit; only the
  attested/cross-vat register (keys-as-caps) needs `valid` to be a succinct in-circuit
  `Verify` — a *sub-fragment*, not a ceiling. Currently a discrete RA (the three core
  laws are stated + proved for `ℕ`/`Excl`); promotion to a *full* step-indexed Iris
  camera (OFE + extension axiom) is for higher-order/recursive resources and would share
  `Boundary`'s `▶` guard.
- **`Metatheory/Confluence.lean`** — **I-confluence (judgement 3)**, the
  invariant-merge property (BEC Thm 3.1): `∀ x y, I x → I y → I (x ⊔ y)` over a
  cell's join-semilattice state. Decides **tier-1 eligibility** (causal-only /
  coordination-free / partition-tolerant) vs escalation to consensus. Independent
  of conservation (`balance ≥ 0` is linear but not I-confluent; a grow-only set is
  I-confluent but not linear). Precedent: Gomes–Kleppmann (SEC in Isabelle),
  Burckhardt, certified-mergeable-RDTs, Katara; CALM/Hydro for compilation.
- **`Metatheory/Laws.lean`** — `Predicate ⊣ Witness` as `Order.GaloisConnection`
  + `HeytingAlgebra`. The verify/find seam typed: `Verify P w : Bool` is the
  decidable, verifier-local side; `find : P → Option W` is the **opaque search
  plugin** (sound-by-verification only; no completeness, no termination).
- **`Metatheory/Authority/Positional.lean`** — the **l4v integrity lift**. `cap`
  datatype + `cap_auth_conferred` + `pas_refined` (authority ⊆ caps, as an
  invariant) + the integrity case-split as the vat-boundary law template
  (`intra` = trivial witness / `cross` = `Discharged P w`). `LossyMorphism`
  (`ρ_in`/`ρ_out`, attenuation-only) as a stated `sorry`'d theorem.

## Candidate-DEPENDENT module — DECIDED: coinductive (A-style)

The **Boundary/Soundness** module ties the abstract `Integrity` relation to an
actual operational model of turns. Its *shape* was the one candidate-dependent
choice; the dregg2 decision (`docs/rebuild/dregg2.md §1.3, §8`) **picks the
coinductive `▶`-guarded bisimulation** over the two alternatives:

- ✅ **coinductive `▶`-guarded bisimulation** (step-indexed / guarded recursion) —
  **CHOSEN**, because a cell is live CODATA (`νF`, `F X = Obs × (AdmissibleTurn ⇒ X)`),
  soundness is behaviour-over-unbounded-time, and checkpoint/replay/time-travel are
  coinductive consequences. The "drifting future" of a non-contractive step is a
  failure mode only a coinductive system has, and `sound_of_step_complete` discharges
  it.
- ✗ explicit operational **step-relation** (small-step `⟶` with a simulation
  invariant) — rejected: would state soundness inductively over `List Turn`.
- ✗ purely **algebraic** characterization (folded-DAG / equational) — rejected.

- **`Metatheory/Boundary.lean`** — scaffolded (`sorry`'d). `TurnCoalg` (the coalgebra
  structure map `c : X → F X`, `F X = Obs × (AdmissibleTurn → X)`); a `▶`-guarded
  `IsBisim`/`Sound` pair (the guard `Later` typed off `previous_receipt_hash`);
  **`theorem sound_of_step_complete`** — soundness ⇔ each step attests the full
  `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` — plus its converse
  `step_complete_of_sound`; and a coinductive `BoundaryRespecting` lifting
  `Authority.Integrity` (intra-trivial / cross-discharged) with the `▶`-guarded
  successor-closed clause.

## §8 caveat — crypto-soundness is NEVER merged into the Lean law

The witness's **cryptographic** soundness (a STARK/circuit obligation: the
`Verify P w : Bool` predicate's binding/extractability) is **never** merged into
the Lean metatheory. The Lean law treats `Verify` as a decidable oracle; the
circuit discharges *that* obligation separately. The Lean↔impl bridge (golden
oracle, differential-harness backend #8) is empirical cross-validation over
`sorry`'d regions, not certification.

## Building

`lakefile.toml` requires mathlib via a local `path` to `../../../src/mathlib4`
(rev `1c2b90b…` @ v4.30.0) to avoid a fresh registry download. **A full mathlib
build is not part of scaffolding** — these files declare the project only.
