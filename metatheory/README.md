# dregg2, in Lean 4 — the metatheory *and* the verification

This directory (`metatheory/`) holds two distinct things that we were, for a long time,
wrongly collapsing into one name:

1. **The actual metatheory** — the candidate-independent *logic of constructive knowledge
   and authority* that dregg is an instance of. Prose in **[`CONSTRUCTIVE-KNOWLEDGE.md`](./CONSTRUCTIVE-KNOWLEDGE.md)**;
   first Lean form in the **`Metatheory.*`** namespace (`Metatheory/ConstructiveKnowledge.lean`,
   `Metatheory/Categorical.lean`).
2. **The verification of dregg2** — the (much larger) Lean library, named **`Dregg2`**
   (sources under `Dregg2/`, root `Dregg2.lean`), built l4v-shaped. *This* is dregg2 as an
   executable, proof-carrying system.

They interact — the verification *discharges* the metatheory's obligations against a real
system — but they are **not the same thing**, and the library was renamed `Metatheory → Dregg2`
to stop hiding that. (See [`docs/rebuild/REORIENT.md`](../docs/rebuild/REORIENT.md) for the
fuller orientation; note it predates the rename and the `Spec` layer.)

A capability here is **constructive knowledge**: to *hold* one is to be able to *exhibit a
witness that verifies* — never merely to assert. Everything below is a projection of that.

Toolchain `leanprover/lean4:v4.30.0`; mathlib via a local `path` require. **It builds**:
`lake build` ⇒ ~3000+ modules, 0 errors, ~25 `sorry` — *all honest*, sorting into exactly the
two buckets in [§ What the sorries mean](#what-the-sorries-mean). The executable layer is
`sorry`-free and `#eval`-able; the new `Spec` layer pins its keystones with `#assert_axioms`.

---

## The layer cake (l4v-shaped, four altitudes)

### 0. The actual metatheory — `Metatheory.*` (candidate-independent)
- **`Metatheory/ConstructiveKnowledge`** — knowledge = a discharging witness exists
  (`holds_iff_discharged_witness`); the verify/find asymmetry (trusted decidable `Verify` ⊣
  untrusted opaque `find`); the **epistemic-boundary lattice** (`verifier_learns_only_acceptance`
  — a ZK verifier sits strictly below content); the generative/restrictive authority duality +
  `no_forge_step`; coinductive `knowledge_does_not_drift`; `knowledge_no_free_copy`.
- **`Metatheory/Categorical`** — *deriving* the abstract spec from categorical first principles:
  conservation as a monoidal functor to a discrete monoid ⇒ no-free-copy; verify/find as a
  Galois connection/adjunction; the cell as a coalgebra, the hyperedge as a (wide) pullback.
  (Research-grade; the goal is "the spec is *derived*, not postulated.")

### 1. Abstract Spec — the laws (`l4v spec/abstract`)
`Core` (symmetric-monoidal cells/turns; **conservation (Law 1)** as a monoid-valued measure),
`Resource`/`StepCamera` (the Iris-camera tier — conservation and authority are *one law*),
`Laws` (`Predicate ⊣ Witness` + the verify/find seam), `Authority/Positional` (the l4v
integrity lift; intra/cross), `Confluence` (I-confluence, the 3rd judgement), `Boundary`
(coinductive soundness over the `νF` cell — the proved keystone is `stepComplete_preserves`),
`Finality` (the 4-tier ordering judgement, `no_downgrade`), `JointTurn` (the cross-cell ⊗ /
`SharedTurnId` pullback ⊗ CG-5 binding), `Privacy`/`Coordination`/`Projection`/`Await`/
`Liveness`/`Upgrade`.

### 2. **`Dregg2.Spec.*` — the factored middle layer (the abstract spec of the *actual*
dregg2 semantics).** This is the new spine: a *small* set of orthogonal primitives that
*generate* dregg1's sprawling catalogs as derived definitions (no flat-coproduct port), with
abstract types throughout (never `Nat` for a hash/commitment).
- **`Spec/Guard`** — ONE verify/find seam unifying authorization ⊣, preconditions, state-
  constraints, and caveats (`firstParty | witnessed | all(∧) | any(OneOf ∨) | gnot`);
  `attenuate_narrows` is the **meet-semilattice** narrowing (*not* a Heyting residual). Legacy
  constraints/auths come back as derived smart-constructors.
- **`Spec/Conservation`** — multi-domain, `LinearityClass`-typed, **value-monoid-parametric**
  conservation: the *same* `Σ = 0` law over cleartext `ℤ` or a commitment group
  (`committed_iff_cleartext` — value hidden yet provably conserved); `multi_domain_independent`.
- **`Spec/Authority`** — the **generative capability graph** (the characteristically-capability
  part): introduce / amplify / mint / endow + attenuate / revoke, governed by Miller's
  *"only connectivity begets connectivity"* (`gen_step_traces` — per-step non-forgeability).
- **`Spec/Lifecycle`** — the **attested dual of creation**: `creation_and_death_are_dual`,
  `archival_is_fold` (the IVC fold as history-compression), and the epistemic asymmetry
  `creation_provable_death_temporal` (birth is exhibitable; distributed death is only leased time).
- **`Hyperedge`** — **the turn is an atomic hyperedge** = the *wide pullback over a shared
  `TurnId`* + N-ary conservation; bilateral / ring / forest are *incidences of one object*.
  `hyperedge_sound` is PROVED (the single-object framing dissolves the `family_joint_sound` knot);
  `Spec/JointViaHyper` derives N-ary joint soundness from it and proves
  **`hyperedge_is_validity_not_canonicity`** (validity = a decidable proof-check; canonicity =
  the separate consensus layer).
- **`Spec/Choreography`** — the blue/red split: **red (coupled) interactions project to a
  hyperedge; blue (I-confluent) commit independently** (`red_projects_to_hyperedge`).
- **`Spec/Await`** — the await family factored: dataflow (promises) ⊕ a temporal `Guard`
  (a `Conditional` = a third-party caveat deferred over time).
- **`Spec/VatBoundary`** — Φ as the named-lossy caps↔keys functor: *permission survives the
  crossing, authority does not* (`forwarded_cap_is_revocable`).

### 3. The portals — the Lean⟷Rust contract (`CryptoKernel`, `World`, `PrivacyKernel`)
Crypto / network-nondeterminism as *uninterpreted interfaces*: proving is parametric over an
abstract `[CryptoKernel …]`; running uses a Rust instance via `@[extern]`. **Crypto-soundness
is the portal's job, never Lean's** (the §8 boundary, below).

### 4. Executable Design Spec + Refinement (`Dregg2.Exec.*`, `Dregg2.Proof.Refine`, `Protocol/*`)
The running machine (`exec`, fail-closed, conservation+authority checked; `sorry`-free,
`#eval`-able), the living record cell (`Exec/RecordCellLive`), the FFI beachhead, and the
`Exec ⊑ Abstract` refinement. *Slated for fundamental rework — as a refinement of the matured
`Spec`, after `Spec` is fully expanded* (Spec-first, then Exec-as-refinement).

---

## <a name="what-the-sorries-mean"></a>What the `sorry`s mean

They sort into exactly two honest buckets — *no gaps masquerade as proofs* (`#assert_axioms`
pins the "PROVED" keystones, erroring on any hidden `sorryAx`):
1. **§8 interface obligations** — the `CryptoKernel`/`World` laws, `conservation_step`, the
   range-proof anti-inflation rib: discharged by Rust + the ZK circuits, *by design* never in
   Lean.
2. **Genuine open theorems** — the deepest coinductive/joint residues (the cross-cell
   bisimulation, the whole-history non-forgeability closure, distributed-death co-witnessability)
   and the Byzantine quorum-intersection / post-GST liveness (they need the adversary/GST model).

## §8 — crypto-soundness is the portal's job, never Lean's
The soundness/extractability of `verify`/`commit`/`hash` is a *circuit* obligation, stated as
`CryptoKernel` *laws*. Lean treats `verify` as a decidable oracle. A boundary, not a gap.

## Building
`lake build` (needs the pinned mathlib). For one file during concurrent swarm work,
`lake env lean Dregg2/<Module>.lean` (race-free; reads oleans, writes none — never `lake build`
mid-swarm). The library is `Dregg2`; the actual-metatheory sibling files (`Metatheory/*.lean`)
verify standalone via `lake env lean` and will get their own `lean_lib`. The outer directory
stays named `metatheory/`.

> The egg metaphor holds: we are learning what is inside without cracking it. What is inside is
> a living, distributed, capability-secure organism that *knows things by being able to prove
> them*, one guarded step ahead of the drifting dark. 🐉🥚
