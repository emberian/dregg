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
`lake build` ⇒ **3042 jobs, 0 errors, 0 cheats, and exactly 3 `sorry`** — and all three are
*by design* (see [§ What the sorries mean](#what-the-sorries-mean)). We drove the count from ~25
down to 3 by a sustained **de-vacuify** discipline: a read-only audit + reconcile-build pass
repeatedly found that "deep" `sorry`s were in fact **false, contradictory, or ill-posed *as
stated*** (e.g. `dead_undecidable` quantified over arbitrary deciders that `Classical.decide`
always supplies; `quorum_intersection`'s bound was self-contradictory; `privacy_by_projection`
was false on open recursion; `hyperedge_sound_bisim` was vacuous over a free `Spec`). Each was
restated *honestly* (strengthen a hypothesis / fix the framing — never gut the conclusion) and
then **actually proved**, several leaving a *proved refutation theorem* behind to record the old
vacuity. Honesty is build-enforced: **`Dregg2/Claims.lean`** re-pins every "PROVED" keystone with
`#assert_axioms` / `#assert_namespace_axioms` (erroring on any hidden `sorryAx` or stray axiom),
and `lake env lean Dregg2/Claims.lean` is the credibility artifact.

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

### 3. The portals + the dischargeable §8 — `Crypto.*`, `World`, `PrivacyKernel`
Crypto / network-nondeterminism as *uninterpreted interfaces*: proving is parametric over an
abstract instance; running uses a Rust instance via `@[extern]`. **Crypto-soundness is the
portal's job, never Lean's** — but the portal is now a *layered, dischargeable contract*, not a
flat oracle:
- **`Crypto.Primitives` (Layer A)** — Poseidon2 `compress` / Pedersen `commit`+`commit_hom`
  (real *algebraic* laws, proved) with *computational hardness* (`collisionHard`/`binding`/
  `unlinkable`) as honest `Prop` **carriers** — replacing the wrong-kind idealized `hash_inj`.
- **`Crypto.VerifierKernel` (Layer B)** — `verify` *defined* as "the extracted circuit is
  satisfiable", with `*_verify_sound` a **derived theorem** (off a `merkle_bridge`-style
  Satisfies↔Relation equivalence), not an assumed oracle.
- **`Crypto.PredicateKernel` (Layer C)** — the `WitnessedKind`s as per-kind `KindObligation`s
  carrying circuit + statement-algebra + a **`Dial` floor**, finally **wiring `EpistemicDial`**
  to the per-kind verifier.
- **Real §8 discharges, end to end (bridge both directions, *no primitive seam*):**
  `Crypto.Merkle` (membership, dial `acceptanceOnly`), `Crypto.Pedersen` (value conservation via
  `commit_hom`, dial `selective`), `Crypto.NonMembership` (sorted-tree neighbor-bracketing). The
  single trust boundary stays exactly the FRI / DLog / Poseidon-CR `Prop` carriers — everything
  above is proved.
`PrivacyKernel` realizes the privacy tiers over the portal; `Privacy`'s graph tier was
de-vacuified into `GraphPrivacyKernel`/`BlindedMembershipKernel` law-carrying classes with
**axiom-free `def` consistency witnesses** (a constructive instance ⇒ the laws can't be
contradictory ⇒ cannot cascade; zero blast radius).

### 4. Executable Design Spec + Refinement (`Dregg2.Exec.*`, `Dregg2.Proof.*`, `Protocol/*`)
The running machine (`exec`, fail-closed, conservation+authority checked; `sorry`-free,
`#eval`-able), the living record cell (`Exec/RecordCellLive`), and the FFI beachhead. The toy
scalar ledger has been lifted to a **content-addressed `Value` record cell** (`Exec/RecordKernel`:
`recCexec_attests`/`recKExec_conserves` re-proved over the named `balance` field), with a second
`Exec ⊑ Spec` refinement square in `Spec/ExecRefinement §3.5`. The **operational LTS** — long the
roadmap's scariest "research" item — is, for the single cell, **complete**: `Proof/LTS`'s
`absStep'_forward` unions the balance-turn and authority-turn forward-simulation squares
(`Exec/AuthTurn` supplies the executable delegate/revoke transition); the residual is the
cross-cell whole-history closure (genuine research, in progress).

### 5. The program logic + userspace verification (`Dregg2.Proof.WP`, `Dregg2.DSL`, `Dregg2.Catalog`, `Protocol/WorkflowGuard`)
This is what makes the system **useful** to a developer, not just sound:
- **`Proof/WP`** — a weakest-precondition / VCG calculus over the `Option`-monad transition
  (`wp`/`Triple`/`vcg`), whose capstone **`vcg_run_sound`** *reduces to the already-proved*
  `stepComplete_preserves` — the run-level soundness was already done; the VCG only *generates*
  the per-turn obligations. Worked: a monotonic counter and a single-ledger escrow.
- **`DSL`** — DSL-A, the `dregg_program {…}` cell-program eDSL: a **parser onto already-proved
  smart-constructors** (no new metatheory), the in-situ-verified replacement for dregg1's external
  `#[dregg_caveat]`/`#[dregg_effect]` macros. The counter/escrow elaborate to their kernel terms by
  `rfl`.
- **`Catalog`** — the metaprogramming spine: `#assert_namespace_axioms` (collapsed the hand ledger),
  the `catalog … where` codegen (emits the smart-ctor + `admits`-characterization + auto-pin triple,
  with a planted `sorry` failing *at generation time*), and the fail-loud `discharge` tactic +
  `Dregg2` aesop rule-set.
- **`Protocol/WorkflowGuard`** — the first verified application's Spec layer (the RDII closed loop):
  the workflow's authorization / ordering / attestation gates re-founded as `Spec.Guard` instances,
  all three **equivalence-proved** down to the running predicate.

---

## <a name="what-the-sorries-mean"></a>What the `sorry`s mean

Only **three** remain, and **all three are by design** — not gaps (`#assert_axioms` pins every
"PROVED" keystone, erroring on any hidden `sorryAx`):
1. **`Core.conservation_step`** — Law 1 stated *spec-first* as the operational obligation the
   executable layer discharges (`Exec.cexec_attests` proves it on the running machine). Open at the
   abstract altitude *on purpose*; closing it there would bake the operational model into the spec.
2. **`Laws.search_sound`** — the verify/find seam's *find* side, undecidable **by design** (the
   whole soundness-by-verification architecture rests on find being an untrusted plugin). Like the
   §8 crypto carriers, this is an interface boundary, not a hole.
3. **`Spec.VatBoundary.phi_functorial`** (abstract) — the full functor coherence between the
   positional and epistemic authority categories; genuinely hard, but a **concrete witness**
   (`phi_functorial_concrete`) is already proved beside it.

Everything else that *used* to be here — the cross-cell bisimulation (single-cell now done via
`Proof/LTS`), distributed-death co-witnessability (a Mathlib halting reduction), the Byzantine
quorum-intersection and post-GST liveness (pigeonhole + an honest assumed `World.gst_liveness`
oracle law) — **has been closed or honestly bounded**. Strikingly, *several of those were false or
contradictory as stated* and only closed once restated honestly (see the de-vacuify note above).
The §8 crypto/`World`-law obligations don't appear here because they enter as **typeclass
parameters / structure fields**, not Lean `sorry`s — the theorems that consume them are genuinely
kernel-clean and *are* pinned.

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
