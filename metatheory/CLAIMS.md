# CLAIMS.md — exactly what dregg2 proves, and what it does not

A skeptic-facing ledger for the `Dregg2` Lean metatheory. It is the **human-readable
half**; the **machine-checked half** is [`Dregg2/Claims.lean`](Dregg2/Claims.lean), which
`import Dregg2` (the root, transitively every module) and then re-pins, in one place, every
keystone advertised as *PROVED / axiom-clean* with `#assert_axioms`. That command (defined in
`Dregg2/Tactics.lean`) ELABORATES TO AN ERROR unless the named theorem's entire axiom set is
`{propext, Classical.choice, Quot.sound}` — in particular it **fails on any `sorryAx`**. So
`lake build` (or `lake env lean Dregg2/Claims.lean`) is itself a credibility artifact: if any
claimed keystone silently regresses to `sorry`, the build breaks **here, at the ledger**, not
somewhere downstream. This is dregg2's Lean-native port of svenvs's `verify-claims.sh` +
`CLAIMS.md` discipline.

> **What "PROVED" means here — load-bearing, not preface.** Exactly the cited theorem and its
> labelled seams. A green ledger is **not** a verified distributed OS, not verified consensus,
> not verified cryptography. It is: *every theorem labelled PROVED is `sorryAx`-free in the
> Lean kernel, modulo the named §8 interface obligations that are, by design, the circuit's
> job and never Lean's.* If "dregg2 is verified" begins to carry more than that, the extra
> meaning is the reader's, not the artifact's.

## Honesty labels

| Label | Meaning |
|-------|---------|
| **PROVED-axiom-clean** | A Lean theorem whose `collectAxioms` is exactly the three standard kernel axioms. No `sorry`, no `admit`, no `axiom`-keyword, no `native_decide`. **Pinned** in `Dregg2/Claims.lean` (build-enforced). |
| **PROVED (home-pinned, parked)** | Identical strength, and self-pinned `#assert_axioms` in its **home module** — but its `.olean` is not yet in `Dregg2/Claims.lean`'s import closure (a concurrent-edit race; see *Parked pins* below). Listed here as PROVED; its central pin is commented out so `lake env lean` stays exit-0, to be re-enabled after an `.olean` rebuild. |
| **rests-on-§8-primitive** | The theorem is real and `sorry`-free *in its own body*, but it is **stated over** an explicit, labelled, literature-standard interface obligation (a `conservation_step`-style operational primitive, or a `CryptoKernel`/`World`/`Verifiable` law). These primitives are `sorry`'d on purpose — they are the circuit's / protocol's job (§8 boundary), never Lean's. A theorem that transitively touches such a `sorry` is NOT `#assert_axioms`-pinned (that would correctly fail). |
| **honest-OPEN** | A genuine open theorem carried as an explicit `sorry` with a one-line in-source reason. Not pinned, not claimed proved. These are the deepest residues (cross-cell/operational bisimulation, Byzantine quorum-intersection, post-GST liveness, distributed-death co-witnessability, the Authority whole-history closure, the topo-sort / functoriality residuals). |

There are **zero `axiom`-keyword declarations** and **zero `native_decide`** in the corpus
(verified by scan). Every `sorry` is one of the two honest buckets below.

## The two honest `sorry`-buckets (and nothing else masquerades as a proof)

1. **§8 interface obligations** — the `CryptoKernel` / `World` laws, `Core.conservation_step`
   (Law 1's balance), `Laws.search_sound` (the soundness-by-verification contract on an opaque
   matcher), the `Privacy` commitment/stealth/nullifier predicates, the range-proof
   anti-inflation rib. Discharged by Rust + the ZK circuits, **by design never in Lean**.
   Soundness/extractability of `verify`/`commit`/`hash` is a *circuit* obligation stated as
   `CryptoKernel` laws; Lean treats `verify` as a decidable oracle. A boundary, not a gap.
   (These enter downstream theorems as **typeclass parameters / hypotheses**, so they do
   **not** appear in `collectAxioms` — a theorem taking them as hypotheses is genuinely
   kernel-clean and IS pinned. Only theorems that contain a `sorry`'d primitive *in their own
   proof term* are excluded.)
2. **Genuine open theorems** — the deepest coinductive/joint/operational residues and the
   adversary/GST-model-dependent distributed claims. Listed explicitly in *§ OPEN* below.

---

## Machine-checked keystones (PROVED-axiom-clean — pinned in `Dregg2/Claims.lean`)

**128 pins** currently build-enforced. Grouped by subsystem (the `Dregg2/Claims.lean` section
numbers). Every row is `collectAxioms`-clean as of the last verification.

| § | keystone (fully-qualified) | module | what it claims |
|---|----------------------------|--------|----------------|
| 0 | `Dregg2.Conserve.sum_conserve_of_deltas_zero`, `…sum_transfer_conserve`, `…sum_indicator`, `…sum_pointUpdate` | `Conserve` | the shared Σ_k conservation lemma library (deltas-sum-zero ⇒ measure preserved; transfer conserves) |
| 1 | `Dregg2.Exec.cexec_attests` | `Exec.StepComplete` | the executable machine attests all 4 `StepInv` conjuncts — realizes `Core.conservation_step` AS A THEOREM about `cexec` |
| 1 | `Dregg2.Exec.conservation_step_realized` | `Exec.StepComplete` | the abstract conservation primitive is discharged by the running kernel |
| 1 | `Dregg2.Exec.livingCell_sound` | `Exec.Cell` | genuine bisimulation of the coinductive living cell to the golden oracle (Mg keystone) |
| 1b | `Dregg2.Exec.RecordCell.recCexec_attests`, `…recReplay_preserves_sumEquals`, `…recordCell_stepComplete`, `…recordCell_run_preserves_sumEquals`, `…recordCell_obs_advances` | `Exec.RecordCell` | the name-keyed record cell GROWS νF life: 4-conjunct step-completeness + conservation over records |
| 2 | `Dregg2.Circuit.bridge` | `Circuit` | satisfied `kernelCircuit` ↔ `fullStepInv` (the circuit-from-Lean CCS bridge) |
| 2 | `Dregg2.Circuit.verify_law_derivable` | `Circuit` | the verify-law is DERIVED from the bridge, not assumed |
| 3 | `Dregg2.Hyperedge.hyperedge_sound` | `Hyperedge` | the atomic hyperedge (turn = wide pullback over shared `TurnId`) is sound given binding |
| 3 | `…hyperedge_sound_needs_binding`, `…hyper_stepComplete`, `…hyper_binding_is_proper`, `Hyperedge.legs_agree`, `…toSharedTurnId`, `…toJointBinding`, `SharedTurnId.toHyperedge`, `ringHyperedge` | `Hyperedge` | leg-agreement, binding-as-proper-subobject, N-ary step-completeness, bilateral/ring as special cases |
| 4 | `Dregg2.Spec.Guard.attenuate_narrows` | `Spec.Guard` | the ONE verify/find rule: attenuation narrows admission (meet-semilattice, NOT Heyting) |
| 4 | `Spec.Guard.admits_all`, `…admits_any`, `…admits_attenuate`, `…admits_witnessed_iff_discharged`, `…discharged_admits`, `…admits_monotonic`, `…admits_sumEquals`, `…admits_senderAuthorized`, `…admits_nonMembership`, `…admits_oneOf` | `Spec.Guard` | the demand⊣supply seam: first-party / witnessed admission, OneOf coproduct, legacy constraints derived |
| 5 | `Dregg2.Spec.committed_iff_cleartext` | `Spec.Conservation` | hidden-yet-conserved: a Pedersen-committed balance conserves iff its cleartext does |
| 5 | `…conservation_over_monoid(_finset)`, `…disclosed_non_conservation`, `…conservative_discloses_nothing`, `…committed_of_cleartext`, `…multi_domain_independent`, `…turnConserves_balance`, `LinearityClass.*` | `Spec.Conservation` | multi-domain, value-monoid-parametric conservation; disclosed-non-conservation exclusivity |
| 6 | `Dregg2.Spec.gen_step_traces` | `Spec.Authority` | the generative core: every new edge of one authorized step traces to an authorized generator ("only connectivity begets connectivity", per-step) |
| 6 | `…introduce_non_amplifying`, `…amplify_needs_held_amplifier`, `…mint_needs_held_factory`, `…mint_conforms_to_contract`, `…confers_refl/trans`, `…{introduce,mint,amplify}_is_gen`, `…{attenuate,revoke}_is_restrict`, `…revoke_step_adds_nothing`, `…gen_conferral_is_attenuation`, `…attenuate_is_restrictive_narrowing`, `…introduce_same_target` | `Spec.Authority` | the capability-graph generators + the per-step half of non-forgeability |
| 7 | `Dregg2.Spec.Lifecycle.creation_provable_death_temporal` | `Spec.Lifecycle` | creation is provable; death is only *temporally* (lease) decidable, never globally |
| 7 | `…creation_and_death_are_dual`, `…archival_is_fold`, `…reclaim_by_lease`, `…terminal_rejects_{effects,transition}`, `…{migrated,destroyed}_terminal`, `…acceptsEffects_iff`, `…isTerminal_iff`, `…birthProvable`, `…archived_still_live` | `Spec.Lifecycle` | lifecycle = attested dual of creation; archival as IVC fold; lease reclamation |
| 8 | `Dregg2.Spec.hyperedge_is_validity_not_canonicity` | `Spec.JointViaHyper` | hyperedge soundness is *validity* (proof-check), distinct from *canonicity* (consensus) |
| 8 | `…joint_via_hyperedge`, `…binary_{binding,joint}_via_hyperedge`, `…singletonHyperedge`, `…validity_is_local_canonicity_is_global` | `Spec.JointViaHyper` | N-ary joint soundness DERIVED from `hyperedge_sound` |
| 9 | `Dregg2.Spec.red_projects_to_hyperedge` | `Spec.Choreography` | the red (coupled) projection of a blue/red split projects to a `Hyperedge` |
| 9 | `…blue_commits_independently`, `…blue_needs_no_hyperedge`, `…red_legs_agree`, `…red_iff_coupled`, `…epp_membrane_is_projection`, `RedBinding.toHyperedge` | `Spec.Choreography` | blue commits independently; red is exactly the coupled fragment |
| 10 | `Dregg2.Spec.Conditional.conditional_is_temporal_guard` | `Spec.Await` | the await family's temporal face IS a `Guard` (conditional = temporal admission) |
| 10 | `…resolve_monotone`, `…expired_stays_expired`, `…resolved_iff_gateway_discharged`, `…gateway_admits_eq_token`, `…await_two_faces`, `…temporal_face_is_await_discharge`, `PromiseGraph.depends_{irrefl,trans}`, `…broken_promise_propagates(_trans)` | `Spec.Await` | temporal Guard ⊕ dataflow DAG; resolution is monotone; broken promises propagate |
| 11 | `Dregg2.Spec.phi_drops_confinement` | `Spec.VatBoundary` | the caps↔keys functor Φ is *named-lossy*: permission survives the vat boundary, authority (confinement) does not |
| 11 | `…forwarded_cap_is_revocable`, `…revocable_iff_not_authority`, `…phi_admits_iff_discharged`, `…cross_vat_needs_witness`, `…macaroon_does_not_cross_phi`, `…biscuit_crosses_phi`, `…phi_domain_is_exactly_biscuit`, `…phi_composes_with_attenuation`, `…phi_attenuation_factors_through_confers` | `Spec.VatBoundary` | biscuit crosses Φ / macaroon does not; Φ composes with attenuation |
| 13 | `Dregg2.Finality.conservation_tier_independent(_iff)` | `Finality` | conservation (Law 1) holds independent of the finality tier — the lattice never weakens it |
| 14 | `Dregg2.Liveness.revocation_needs_consensus` | `Liveness` | revocation (unlike GC collection) requires consensus — the asymmetry of the two deaths |
| 15 | `Dregg2.Exec.Consensus.{quorum_reaches_bft_tier, committedByQuorum_reaches_bft_tier, below_quorum_not_bft, net_no_downgrade(_via_world), finality_monotone_on_net, quorum_grows_preserves_finality, committed_holds_along_rounds, cross_tier_join_on_net, NetCell.tier_eq_bft_iff}` | `Exec.Consensus` | quorum→finality-tier bridge: a reached quorum lands in the BFT tier; finality is monotone on a growing net (**Byzantine *safety* itself stays OPEN — see below**) |
| 16 | `Dregg2.Upgrade.upgrade_never_bricks`, `…stale_version_falls_back_to_signature` | `Upgrade` | anti-brick `set_program`: a stale AIR_VERSION falls back to owner signature; never bricks |
| 17 | `Dregg2.Proof.{refine_conservation(_measure), refine_run_conservation, refine_integrity(_intra)}` | `Proof.Refine` | Exec ⊑ Abstract: conservation + intra-vat integrity refine (**full simulation diagram OPEN**) |

(Ellipses abbreviate same-module siblings; every name is spelled out and pinned individually in
`Dregg2/Claims.lean`.)

---

## Parked pins (PROVED in source / home-pinned, not yet in the central closure — a race, not a gap)

These keystones are **`sorry`-free in source and self-pinned `#assert_axioms` in their home
module**, but their `.olean` is not yet in `Dregg2/Claims.lean`'s transitive import closure as
built — a concurrent-swarm artifact (the root `Dregg2.lean` gained an import, or a source file
was edited, after the live `.olean`s were produced; this agent must not `lake build` mid-swarm).
Their central pins are **commented out** in `Dregg2/Claims.lean` so `lake env lean` stays exit-0,
with a note to re-enable after an `.olean` rebuild. They are PROVED — they are simply parked.

| keystone | module | why parked |
|----------|--------|-----------|
| `Dregg2.Spec.guard_is_authority_conferral`, `…conferralGuard_admits_self`, `…introduce_passes_conferralGuard`, `…conservation_is_hyperedge_cg5`, `…hyperedge_conserves_crossCell`, `…lifecycle_revoke_is_authority_restrictive`, `…revoke_is_terminal_restrictive`, `…migrated_and_destroyed_both_revoke`, `…choreography_red_conserves(_sum)`, `…guard_attenuate_narrows_is_meet`, `…authority_confers_narrows_is_meet`, `…attenuation_is_one_order`, `…guard_meet_is_authority_meet` (§12, `Spec.Coherence` — the cross-subsystem weave: one attenuation order, guard-meet = authority-meet) | `Spec.Coherence` | `Dregg2.Spec.Coherence`'s import was added to the root after the last `Dregg2.olean`; its `.olean` was not present in closure at verification time |
| `Dregg2.Upgrade.{invariant_intro, safety_preservation, admit_preserves_safety, self_improvement_is_safe, genealogy_sound, identity_vouch_unconditional, upgradeGenealogy_sound, signatureVouchUnbrickable}` (§16 Envelope spine: invariant intro, safety preservation under policy-admit, self-improvement-is-safe, genealogy soundness) | `Upgrade` | the live `Upgrade.olean` predates the source edit that added/renamed these Envelope theorems |

---

## OPEN (honest — genuine open theorems, carried as labelled `sorry`, NOT proved, NOT pinned)

| open theorem | module | what is still needed |
|--------------|--------|----------------------|
| `Dregg2.Spec.only_connectivity_begets_connectivity` (the Authority **whole-history closure**) | `Spec.Authority` | **`collectAxioms` = `[sorryAx]` — confirmed DIRTY.** The per-step core `gen_step_traces` IS proved-clean; the whole-history non-forgeability closure over `Reachable` (the `attenuate`-adds-a-narrowed-edge case across the full step history) is NOT. A docstring nearby calls it "PROVED, closed" — that is an **overclaim**; the theorem still inherits `sorryAx`. |
| `Dregg2.Liveness.dead_undecidable` | `Liveness` | genuine undecidability of global deadness — needs a Turing/computability model (diagonalization against every `decide : … → Bool`) absent from the imports |
| `Dregg2.Spec.Lifecycle.distributed_death_not_co_witnessable` | `Spec.Lifecycle` | the same FIND-side undecidability: distributed death is co-semi-decidable at best under asynchrony+partition+graph-privacy; the lease fallback (`reclaim_by_lease`) is the provable alternative |
| `Dregg2.World.quorum_intersection_safety_OPEN` (Byzantine **quorum intersection / safety**) | `World` | the adversary/honesty model + conflict semantics + the n>3f arithmetic; belongs with the protocol that owns the honest-set semantics, not the bare network oracle |
| `Dregg2.World.liveness_after_gst_OPEN` (**post-GST liveness**) | `World` | the partial-synchrony / GST bound + honest-supermajority assumption; asynchrony is the adversary's, not a law of the `World` interface |
| `Dregg2.Hyperedge` Sound-of-step-complete at N-ary (`Sound T (Spec i) …`) and `hyper_not_all_admissible` | `Hyperedge` | the **cross-cell / operational bisimulation** at N-ary, and the proper-subobject obstruction for general `Fintype ι` (the binary case `hyper_binding_is_proper` IS proved) |
| `Dregg2.Coordination` projection-progress (Carbone–Montesi) + the `mu`-recursion projection case | `Coordination` | the reachable-LTS operational machinery (`Dual` partner among reachable configs) / a closedness hypothesis on `G` |
| `Dregg2.Spec.Conditional.pipeline_topological` (the topo-sort) | `Spec.Await` | the Szpilrajn linear-extension `Finset` topological sort; the load-bearing antecedent (strict partial order ⇒ an order *can* exist) IS proved |
| `Dregg2.Spec.phi_functorial` (Φ **functoriality**) | `Spec.VatBoundary` | the full two-category coherence: one concrete non-degenerate `Verifiable` witnessing `preserves_id` + `lossy_on_confinement` + `preserves_comp` simultaneously |

---

## rests-on-§8-primitive (real, `sorry`-free in body, but stated over a labelled interface obligation)

These are **not** OPEN and **not** overclaims — they are the §8 boundary, by design. The
primitive itself is a `sorry`'d / typeclass-parameter obligation that Rust + the ZK circuits
discharge. A downstream theorem that takes the primitive as a **hypothesis / typeclass
parameter** is kernel-clean and IS pinned above (it does not touch `sorryAx`); a theorem whose
**own body** invokes the primitive is excluded from the pins and lives here.

| primitive (the labelled obligation) | module | who discharges it |
|-------------------------------------|--------|-------------------|
| `Dregg2.Core.conservation_step` (Law 1's balance: turns move/withhold/erase but never create/destroy units) | `Core` | the operational semantics / the circuit; **realized as a theorem** downstream by `Exec.cexec_attests` (which IS pinned) |
| `Dregg2.Laws.search_sound` (soundness-by-verification: whatever an opaque matcher returns must verify) | `Laws` | the external prover/matcher plugin (untrusted; verifier is TCB) |
| `Dregg2.CryptoKernel` laws (`verify`/`commit`/`hash` soundness & extractability) | `CryptoKernel` (typeclass) | the ZK circuits + Rust portal — enter downstream as typeclass params, so downstream theorems stay clean |
| `Dregg2.World` laws (network/clock/randomness oracle) | `World` (typeclass) | the protocol + partial-synchrony model |
| `Dregg2.Privacy.{derivedFrom, Indistinguishable, memberOf, memberView, ViewIndistinguishable, nullifierOf, UnlinkableToHolder, LegalDerivation}` (stealth/commitment/nullifier predicates + the unlinkability/anti-double-spend laws stated over them) | `Privacy` | the cryptographic carriers (DH derivation, Pedersen commitments, range proofs) — the anti-inflation rib is a circuit obligation |

---

## How to re-check (race-safe, mid-swarm)

```
cd metatheory
lake env lean Dregg2/Claims.lean   # must exit 0 — reads oleans, writes none; NEVER `lake build` mid-swarm
```

Exit 0 ⇒ every pinned keystone is `sorryAx`-free. A non-zero exit with an `unknownConstant`
means a parked pin's `.olean` rebuilt (re-enable it) or a keystone was renamed; a non-zero exit
with an *axiom-hygiene FAIL* means a claimed keystone silently inherited a `sorry` — fix the
proof or move the row to **OPEN** above. That breakage, at the ledger, is the whole point.
