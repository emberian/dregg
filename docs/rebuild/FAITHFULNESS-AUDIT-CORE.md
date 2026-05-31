# FAITHFULNESS / VACUITY AUDIT — the PRE-session core corpus

**Scope.** Adversarial, read-only audit of the **pre-session** dregg2 Lean corpus that
`FAITHFULNESS-AUDIT.md` (this-session-only) never touched: `Core`, `Boundary`, `JointTurn`,
`Resource`, `Confluence`, `Finality`, `Execution`, `Laws`, the `Authority/*` family,
`CryptoKernel`, `PrivacyKernel`, `Privacy`, `Spec/*` (≠ ExecRefinement), `World`, and the
`Proof/*` modules (`BFT`, `BFTLiveness`, `Synchronizer`, `BeaconSpace`(+`Interior`),
`CoinductiveAdversary`, `ContendedCrossCell`, `CrossCellLTS`, `ForestLTS`, `WPCatalog`).
Nothing modified. Mandate: `#assert_axioms`/"0 sorries" proves **kernel-cleanliness**, NOT
**non-vacuity** or **fidelity**. This ledger surfaces what the goal-sensor cannot see.

**Headline.** The pre-session core is, on the whole, **substantially MORE genuine than the
this-session executable layer** the prior audit covered — there is no `ExecRights := Unit`
collapse here; the authority spine (`CDT`, `Caveat`, `Blocklace`) uses *real* `Finset`/`List`
rights and causal-order lattices, and the BFT safety + cross-cell contention results are real
counting/commutation proofs. The vacuity in this corpus is concentrated in **three specific
patterns**: (1) **portal-shaped theorems whose body IS a hypothesis field** (the entire
`Privacy` graph tier, `Predicate.registry_sound`, the consensus *liveness* chain); (2) **`= rfl`
definitional tautologies the docstrings themselves flag as repaired-but-still-empty**
(`Finality.conservation_tier_independent`); and (3) **"detection/irreducibility" theorems that
merely re-project their own hypothesis** (`Blocklace.equivocation_detectable`). The single
systemic illusion is the **consensus-liveness chain**: a tower of genuine math
(`Synchronizer`'s geometric series, `BeaconSpace`'s measure-0 tail) that **never connects to the
protocol**, because the load-bearing step (`Pacemaker.responsive_quorum`) *assumes the quorum
forms*.

---

## 0. The three by-design sorries — CONFIRMED honest

A whole-corpus grep finds exactly **three** real `sorry` bodies (plus one in `Liveness.lean`,
out of scope; `Privacy:253` is prose; `Boundary.boundary_respecting_sound`'s docstring says
"Stated sorry" but the body is `exact hbr.admissible x hx t` — **stale docstring, actually
PROVED**).

| sorry | verdict | why honest |
|---|---|---|
| `Core.conservation_step` (`Core.lean:162`) | **BY-DESIGN OK** | Law 1's balance is an axiom-style obligation the *operational model* discharges; there is genuinely no data in `Conservation`/`Turn` from which it follows in-module. The three corollaries (`conservation_ordinary`, `mint_delta`, `burn_delta`) and `withholding_no_free_copy` are PROVED *from* it — so the sorry is a real load-bearing primitive, not a hidden vacuity. |
| `Laws.search_sound` (`Laws.lean:60`) | **BY-DESIGN OK** | `Searchable.find` is an opaque external prover plugin; soundness-by-verification is a *contract on the plugin*, with no in-module relation between `find` and `Verify` to derive it from. The honest content lives in `Predicate.adversarial_find_cannot_forge` (quantifies over the prover) and `find_untrusted` (real `∃`). |
| `Spec.VatBoundary.phi_functorial` (`VatBoundary.lean:401`) | **BY-DESIGN OK** | Genuinely blocked over an *abstract* `Verifiable`: `preserves_id` needs an accepting witness (an abstract `Verify` may accept none), `lossy_on_confinement` needs a non-injective `stmtOf`. A CONCRETE non-degenerate witness `phi_functorial_concrete` is proved axiom-clean alongside. The sorry is localized and the loss is independently witnessed by the §4 keystones. |

All three are honest. None hides vacuity.

---

## 1. Per-module verdict tables

Verdicts: **GENUINE** / **PARTIALLY-VACUOUS** / **VACUOUS** / **PORTAL-OK** (honest carried
`Prop`-assumption) / **TAUTOLOGY** (`= rfl`, near-zero semantic content).

### `Core.lean` — the conservation monoid

| theorem | verdict | why |
|---|---|---|
| `conservation_step` (:154) | **PORTAL-OK** (the one Law-1 primitive) | see §0. |
| `conservation_ordinary`/`mint_delta`/`burn_delta` (:166/176/187) | **GENUINE** | real algebra off `conservation_step` + the `*_pure` fields. Non-trivial (`mint_delta` reads the actual `minted` inflow). |
| `withholding_no_free_copy` (:209) | **GENUINE** | the `[IsCancelAdd M]` hypothesis is the honest extra datum; `count A = count A + count A ⇒ count A = 0` via `left_eq_add` is real linearity content, and the typeclass premise is load-bearing (false in `ℕ∞`). |
| `example : Conservation ℕ` (:137) | **GENUINE (inhabitation)** | constant-0 measure witnesses the fields are satisfiable — non-vacuity of the structure. |

### `Boundary.lean` — the coinductive vat-boundary

| theorem | verdict | why |
|---|---|---|
| `Later Q := Q` (:103) | **DEGENERATE TYPE (flagged)** | the `▶` guard is **definitionally the identity**. Every theorem that "uses the `▶` guard" (`IsBisim.step_rel`, `BoundaryRespecting.closed`) is therefore over an *unguarded* recursion. The module is candid this is a "Prop-level placeholder", but it means the corpus's coinductive-productivity story is *asserted in prose*, not modeled — `Later` does no work. |
| `stepComplete_preserves` (:177) | **GENUINE** | the honest replacement for the retired-as-false `sound_of_step_complete`. Real safety-invariant lift via `Execution.invariant_run`. The load-bearing keystone. |
| `bisim_eq` (:203), `sound_refl` (:211) | **GENUINE but WEAK** | only **reflexivity** ("every cell is bisimilar to itself"). The module openly says the soundness-from-step-completeness content is in `stepComplete_preserves`, not here. `Sound` is an equivalence notion whose only proven inhabitant is the diagonal. |
| `boundary_respecting_sound` (:244) | **GENUINE** (docstring stale) | body is `exact hbr.admissible x hx t` — a real projection, not a sorry. But note it just *re-projects* the `BoundaryRespecting.admissible` field (see pattern §3.B). |

**Honesty credit:** the module *deleted* two theorems it found false-as-stated (`sound_of_step_complete`/`step_complete_of_sound`, refutable at `Spec.Carrier = Empty`) and says so. That is exemplary.

### `JointTurn.lean` — cross-cell atomic turn

| theorem | verdict | why |
|---|---|---|
| `SharedTurnId.agree` (:112) | **GENUINE** | `agree₁.trans agree₂.symm` — real equalizer condition from two legs. |
| `joint_stepComplete` (:197), `joint_sound` (:230) | **GENUINE** | componentwise assembly of two step-complete coalgebras, then `stepComplete_preserves` on the product. Real. |
| `joint_sound_needs_binding` (:271), `binding_is_proper` (:333) | **GENUINE (negative)** | a real `¬∀`/`∃¬`: two one-state cells with half-edges `1`,`1` give CG-5 `1+1=2≠0`, so the product state is **not** `JointAdmissible`. `by decide` over a concrete witness; the binding is load-bearing. Honest **self-correction**: the docstring retracts the prior `tensor_not_final` as *mis-stated* (product of finals IS final) and replaces it with the correct proper-subobject fact. |
| `atomicity_as_proof` (:392) | **GENUINE (thin)** | `JointCommit ↔ willSucceed` is `and_congr (gate₁) (gate₂)` — true, but the `gateᵢ` hypotheses (`committed ↔ LocalSucceeds`) **are** the content; the theorem is a congruence over assumed biconditionals. Low marginal content but honest. |
| `family_joint_sound` (:458), `family_atomicity` (:482) | **GENUINE** | N-ary `Finset.sum` version; `b.balanced` supplies the conservation half. Both hypotheses load-bearing. Honest note that a prior free-`Spec` form was false. |

### `Resource.lean` — the camera tier

| theorem | verdict | why |
|---|---|---|
| `ℕ`/`Excl`/`Auth` `ResourceAlgebra` instances | **GENUINE** | the docstring claims `Auth`'s laws are `sorry`'d — **this is stale**; `Auth`'s `op_comm`/`op_assoc`/`valid_op_left`/`core_*` are all **fully proved** (`:235-288`). Real camera laws. |
| `Fpu.refl`/`Fpu.trans` (:114/118) | **GENUINE** | real FPU algebra. |
| `excl_no_dup` (:185) | **PARTIALLY-VACUOUS** | "no exclusive composes with itself validly" — but `Excl.op _ _ = invalid` for **all** pairs (`:163`), so `¬ valid (a ⊙ a)` holds for the *same trivial reason* `¬ valid (a ⊙ b)` would: the "non-duplication" is not specific to self-composition, it is that *nothing* composes. The NFT story ("a cannot be in two places") is true but the theorem proves the weaker "exclusives never compose at all". |
| `fpu_of_total` (:144) | **GENUINE (honest)** | candidly states the non-triviality of conservation lives entirely in `valid`; in a total camera every update is an FPU. |
| `conservation_is_fpu` (:296) | **GENUINE** | real case-split on the `Auth` frame; the `hmono` hypothesis is the genuine "deposit needs headroom" content. |
| `ConfinesAuthority := Fpu` (:319) | **DEFINITION (honest)** | "authority = conservation" stated as a *definition*, explicitly not a proved `↔`. Honest — but it means the unification is *asserted by fiat*, not derived. |

### `Confluence.lean` — I-confluence (third judgement)

| theorem | verdict | why |
|---|---|---|
| `admits_sound` (:58) | **GENUINE (thin)** | `h x y hx hy` — re-applies the `Tier1Eligible = IConfluent` hypothesis. Content is the *definition*, not the theorem. |
| `nonpairwise_escalation` (:70) | **GENUINE** | classical `¬IConfluent ⇒ ∃` clashing pair. Real contrapositive. |
| `top_iconfluent` (:95), `cardLeOne_not_iconfluent` (:104) | **GENUINE (the crown)** | both directions of the dichotomy WITNESSED over `Finset ℕ`: `True` is I-confluent; `card ≤ 1` is NOT (`{1}⊔{2}={1,2}`, `by decide`). This is the *real falsifiability* that makes I-confluence non-vacuous, and it is reused widely (`ContendedCrossCell`, `Credential`). |

### `Execution.lean` — the run algebra

| theorem | verdict | why |
|---|---|---|
| `Run.trans`/`Run.snoc` (:49/55), `invariant_run` (:65), `safe_of_stepInvariant` (:78) | **GENUINE** | pure, fully-proved induction over the reflexive-transitive closure. Protocol-independent. The reusable backbone the whole corpus's safety results lean on. No vacuity. |

### `Finality.lean` — the tier ladder (second judgement)

| theorem | verdict | why |
|---|---|---|
| `Tier` `LinearOrder`, `rank_injective` (:84) | **GENUINE** | real 4-element total order. |
| `tau_unified_tier` (:193), `tier1_requires_iconfluent` (:204) | **GENUINE (hypothesis-routed)** | both take the well-formedness / classifier-soundness as explicit hypotheses (`hwf`, `hsound`) and apply them. Honest: the docstring of `tier1_requires_iconfluent` admits "an arbitrary `I` is not I-confluent for free — the *classifier* is what guarantees it". So the theorem is "the classifier says so ⇒ it's so". |
| `commit_at_join_of_tiers` (:237), `no_downgrade` (:280) | **GENUINE** | `no_downgrade` is a real `invariant_run` lift over `finalitySystem` (tier monotone non-decreasing); `commit_at_join_of_tiers` has a real fold-max-dominates induction. Strong. |
| `conservation_tier_independent` (:335) | **TAUTOLOGY (self-flagged)** | `conservedAtTier t₁ f = conservedAtTier t₂ f` proved by **`rfl`**, because `conservedAtTier` **discards** its `Tier` argument. The docstring is candid this *repaired* a worse `iff_of_true` version — but the repair is still "two definitionally-identical propositions because the tier never enters". The genuine content (`conservedAtTier_holds`, that the verdict IS Law 1's balance) is a *separate* theorem; this one is `x = x`. |

### `Laws.lean` — the verify/find seam

| theorem | verdict | why |
|---|---|---|
| `search_sound` (:53) | **PORTAL-OK** | see §0. |
| `polarity_galois` (:75) | **GENUINE** | real Birkhoff/formal-concept Galois connection — fully proved over an arbitrary relation. Substantive. |
| `predicate_witness_galois` (:101) | **GENUINE** | instantiates `polarity_galois` at `Discharged`. The docstring notes it *replaces a prior placeholder that was false as stated*. Honest. |
| `predicate_heyting` (:111) | **GENUINE** | `le_himp_iff.symm` — the real residuation justifying attenuation. |

### `CryptoKernel.lean` — the §8 crypto portal

| theorem | verdict | why |
|---|---|---|
| `CryptoKernel` class | **PORTAL-OK** | `verify` opaque `Bool`; `collisionHard : Prop` is the **correct kind** of carrier (the docstring fixes a prior `hash_inj : Injective` to a `Prop` collision-resistance carrier — honest crypto modeling). `commit_hom` is the one genuine algebraic law. |
| `discharged_iff_verify` (:75) | **TAUTOLOGY** | `Iff.rfl` — `Discharged` unfolds *definitionally* to `verify = true`. Zero content beyond unfolding. |
| `cross_vat_via_verify` (:87), `intra_vat` (:96) | **GENUINE (thin)** | constructors `Integrity.cross proof h` / `Integrity.intra hown` — they *package* the §8 verify result into the integrity relation. Real bridge but each is a one-constructor application. |
| `Reference` instance (:125) | **DEGENERATE WITNESS (honest)** | `verify := decide (stmt = proof)`, `commit v r := v+r`, `collisionHard := True`. Inhabits the interface (so parametric theorems aren't vacuous) but is a *toy* — `commit_hom` holds because `commit` is literally `+`. Honestly labeled a TEST stand-in. |

### `Authority/Positional.lean` — the l4v integrity lift

| theorem | verdict | why |
|---|---|---|
| `boundary_law` (:152) | **GENUINE (hypothesis-routed)** | the real "this is an admissible kernel transition" obligation enters as the `adm` hypothesis (intra ∨ ∃ discharged witness); the theorem is the l4v case-split that maps it to `Integrity`. Faithful to `integrity_obj_atomic`, but the *admissibility* is assumed, not derived. |
| `confinement_preserved` (:170) | **GENUINE** | `noGrow : ∀ s, caps' s ⊆ caps s ⇒ PasRefined preserved`. Real subset-transport; `noGrow` is the honest "turn never adds a cap" premise. |
| `lossy_attenuation_only` (:203) | **GENUINE** | the docstring fixes a prior version where `in_le`/`out_le` were missing (making it unprovable); now attenuation is a *structure field*, so the theorem is `⟨m.in_le, m.out_le⟩` — true, but the content is "the structure carries its own proofs". Honest self-repair. |

### `Authority/Caveat.lean` — the token/macaroon layer

| theorem | verdict | why |
|---|---|---|
| `attenuate_narrows` (:90), `attenuate_subset` (:98) | **GENUINE (strong)** | real `List.all_append` — adding a caveat genuinely shrinks the admitted set. The one rule the system rests on, *actually* proved on the concrete chain. No Unit collapse. |
| `attenuate_trivial` (:105) | **GENUINE (sanity)** | always-true caveat = identity. |
| `macaroon_not_crossvat`/`biscuit_crossvat` (:119/124) | **GENUINE (thin)** | `rw [h]` on a 2-case discriminant. True, low content. |
| `token_discharges` (:142) | **TAUTOLOGY** | `:= h` — `Discharged` unfolds to `admits = true`, which is the hypothesis. Definitional. |
| `#eval` demos | **GENUINE (executable witnesses)** | real windowed-biscuit narrowing computed. |

### `Authority/CDT.lean` — the capability-derivation tree (THE authority spine)

| theorem | verdict | why |
|---|---|---|
| `edge_attenuates` (:133), `path_narrows`/`path_attenuates` (:153/174) | **GENUINE (crown jewel)** | real `Finset Auth ⊆` rights lattice; `path_attenuates` is a genuine **induction over `DerivationPath`** chaining `⊆`-transitivity. This is the antidote to the this-session `ExecRights := Unit` collapse — authority attenuation proved on a REAL lattice. |
| `amplifying_rejected` (:192), `badCDT_rejected` (:311) | **GENUINE (negative)** | the invariant *has teeth*: a `decide`-checked amplifying edge makes the CDT not-well-formed. |
| `chain_renders_path`/`chain_edge_is_subset`/`cdt_edge_is_subset` (:218/228/238) | **GENUINE** | the CDT⟷biscuit bridge reuses `attenuate_narrows` — real shared narrowing law. |
| `goodCDT_wellFormed` (:281), `goodCDT_keystone` (:305) | **GENUINE** | the keystone *derived* (not just `#eval`'d) on a concrete store-resolved path. |

### `Authority/Blocklace.lean` — the byzantine-repelling DAG

| theorem | verdict | why |
|---|---|---|
| `lookup_of_mem` (:106), `demo_precedes_left_g0` (:441) | **GENUINE** | real induction on the lace / on `precedes`. Substantive DAG-structure facts. |
| `equivocation_detectable` (:198) | **PARTIALLY-VACUOUS (re-projection)** | `⟨⟨a,b,e⟩, e.incomp⟩` — it **re-projects its own hypothesis**: `Equivocation` already *contains* `incomp` and the two blocks, and the theorem just repackages them as `Equivocator ∧ …`. It proves "if you hand me an equivocation, I can hand you back an equivocator" — true, but content-free as a *detection* claim (the detection is the hypothesis). |
| `observer_detects` (:210) | **PARTIALLY-VACUOUS (re-projection)** | `⟨e, hsee.1, hsee.2⟩` — same: re-projects `e` and `hsee`. |
| `honest_no_equivocation` (:238), `honest_chain_implies_comparable` (:250) | **GENUINE** | real contrapositive: `HonestChain` (total `≺`-order) ⇒ no incomparable pair ⇒ `¬Equivocator`. The honest content. |
| `cdt_is_blocklace` (:338) | **GENUINE** | real induction transporting a `DerivationPath` to a `≺`-chain. The "CDT ≡ blocklace" bridge, proved. |
| `attested_mono` (:380) | **GENUINE** | real `Nodup.subperm.length_le` monotonicity — finality never regresses. |
| `demo_equivocation`/`demo_detect` (:475/482) | **GENUINE** | concrete 4-block lace with a `decide`-checked fork. This is where the *real* detection content lives (the general theorem just re-projects; the demo actually exhibits a caught fork). |

### `Authority/Predicate.lean` — the verifier-registry seam

| theorem | verdict | why |
|---|---|---|
| `discharged_iff_registryVerify` (:93), `registry_sound` (:106) | **TAUTOLOGY** | both `Iff.rfl`/`:= haccept` — `Discharged` at the registry instance unfolds *definitionally* to `registryVerify = true`. "Soundness-by-verification" is literally "accept = accept". Zero content beyond unfolding. (The docstring calls this THE KEYSTONE; the genuine content is elsewhere.) |
| `registry_sound_find` (:118) | **TAUTOLOGY + decoration** | `_hfound` unused; reduces to `registry_sound`. |
| `adversarial_find_cannot_forge` (:151) | **GENUINE** | quantifies over **every** prover `find` and shows acceptance is impossible if the verifier rejects. THIS is the real soundness content (the prover never appears in the conclusion). |
| `find_untrusted` (:138) | **GENUINE (negative)** | real `∃` exhibiting `find = none` while a witness verifies — no-completeness, by construction. |
| `custom_distinct_vk` (:187), `crypto_kind_routes_to_oracle` (:217) | **GENUINE** | real content-addressing separation / oracle routing. |

### `Authority/Credential.lean` — verifiable credentials

| theorem | verdict | why |
|---|---|---|
| `credential_verifies_iff_issued_and_not_revoked` (:165) | **GENUINE** | real `&&` decomposition; both directions. The §8 oracle (`CryptoKernel.verify`) is honestly a carried term, never reasoned into. |
| `revoke_blocks_verify` (:191), `isRevoked_revoke!` (:181) | **GENUINE** | real `Finset.mem_insert_self` — revocation actually flips the bit. |
| `revocation_is_iconfluent`/`revocation_tier1_eligible`/`revocation_invariant_nontrivial` (:226/235/242) | **GENUINE** | reuses `NullifierCell`'s monotone invariant `fun s => rev₀ ⊆ s` — a **falsifiable** no-loss property (witnessed non-trivial), NOT `fun _ => True`. Honest de-vacuification. |
| `mergeRevocations_membership` (:251) | **GENUINE** | real CvRDT union membership. |

### `Authority/Discharge.lean` — the await authority-face

| theorem | verdict | why |
|---|---|---|
| `caveat_ok_mono` (:63), `admits_mono_discharge` (:86), `admits_mono_subset` (:97) | **GENUINE** | real `List.all` monotonicity under the accumulating-discharge order. "Resolve forward, never un-resolve" actually proved. |
| `resolve_forward` (:149), `awaiting_resolves` (:168) | **GENUINE** | real `settle`-then-`admits` with `List.all_append`. Substantive. |
| `Later`-guard note | n/a | this module models the ▶ guard honestly via the `Discharges.le` order (unlike `Boundary.Later := Q`). |

### `Privacy.lean` — the three privacy tiers

| theorem | verdict | why |
|---|---|---|
| `field_projection_hides_private` (:101) | **GENUINE** | real selective-disclosure: projection independent of private-field values. Fully proved, no portal. |
| `committed_conservation` (:160), `commit_sum`/`commitHom`/`commitHom_sum` | **GENUINE** | real `Finset` homomorphism sum off the `Commitment.homomorphic` field. The value tier is genuine algebra. |
| `committed_conservation_of_core` (:221), `committed_conservation_is_fpu` (:236) | **GENUINE** | real bridges to `Core.conservation_ordinary` and `Resource.Fpu.refl`. |
| `unlinkable` (:395), `zkauthchain_sound` (:405), `blinded_membership_hides_element` (:416), `nullifier_hides_identity` (:451) | **PORTAL (the graph tier)** | each body **IS** a `GraphPrivacyKernel`/`BlindedMembershipKernel` law-FIELD. The only inhabiting instance (`graphRef`, `:489`) sets `Indistinguishable := fun _ _ => True`, `UnlinkableToHolder := fun _ => True`. So every graph-tier privacy theorem is, **in its only model, `True`**. Honestly labeled portal (the prior `:= sorry` was strictly worse — it was `sorryAx Prop`), and `graphRef` is a `def` not an `instance` to prevent silent resolution. But: this is NOT proof of stealth/anonymity; it is "the interface is inhabitable". |
| `nullifier_prevents_double_spend` (:434), `anonymity_nullifier_reconciliation` (:461) | **GENUINE (the spend half) + PORTAL (the anonymity half)** | the double-spend gate is real Bool logic; the anonymity conjunct is the portal field. |

### `PrivacyKernel.lean` — privacy over the CryptoKernel portal

| theorem | verdict | why |
|---|---|---|
| `commit_zero` (:52) | **GENUINE** | actually **DERIVED** from `commit_hom` via `AddCommGroup` cancellation — not added to the interface. Real. |
| `commitHom`/`commit_sum_kernel` (:69/81), `committed_conservation_kernel` (:108) | **GENUINE** | real `map_sum` over the portal's `commit_hom` LAW. Stronger than `Privacy.lean`'s version (the hom is a *proved interface consequence*, not a postulated structure field). |
| `nullifier_no_double_spend` (:147), `nullifier_deterministic` (:160) | **GENUINE (thin)** | real Bool logic + function-ness. `nullifier_deterministic` is `rw [h]` (trivial but honestly named load-bearing). |

### `Spec/Conservation.lean` — multi-domain conservation

| theorem | verdict | why |
|---|---|---|
| `LinearityClass.*_iff`, `paired_and_disclosed_exclusive` (:128-142) | **GENUINE** | real exhaustive case-splits; the disjointness of the two classifiers is the soundness backbone. |
| `conservation_over_monoid`(`_finset`) (:220/229) | **GENUINE** | real `AddCommMonoid` `Σδ=0 ⇒ pre+Σ=pre`. The generalization of Core to a commitment group. |
| `disclosed_non_conservation` (:273), `conservative_discloses_nothing` (:288) | **GENUINE** | real `Receipt.WellFormed` structural binding. |
| `committed_of_cleartext` (:325), `committed_iff_cleartext` (:337) | **GENUINE (strong)** | the **backward** direction genuinely consumes `Function.Injective h` (binding) — the verifier-trusts direction. The hom + injectivity are honest hypotheses, not axioms. The §8 range-proof gap is named (`RangeObligation`, :419), not papered over. |
| `multi_domain_independent` (:378) | **GENUINE** | real both-directions conjunction; no cross-domain leakage. |

### `Spec/VatBoundary.lean`

| theorem | verdict | why |
|---|---|---|
| `cross_vat_needs_witness`/`phi_drops_confinement`/`forwarded_cap_is_revocable`/`macaroon_does_not_cross_phi`/`biscuit_crosses_phi`/`phi_composes_with_attenuation` | **GENUINE** | the concrete crossing facts (not read in full, but the structure is real Guard/Token reuse). |
| `phi_functorial` (:392) | **BY-DESIGN sorry** | see §0; `phi_functorial_concrete` proved alongside. |

### `World.lean` — the network/clock/randomness portal

| theorem | verdict | why |
|---|---|---|
| `World` class (`recv_mono`, `gst_liveness`) | **PORTAL-OK / PORTAL-SUSPECT** | `recv_mono` is an honest append-only-log law. `gst_liveness` (:115) is the suspect: its **conclusion is essentially the productivity premise** — "if the distinct-voter count grows without bound (`hprod`) then a threshold-meeting round exists" — and the Reference instance (:400) discharges it by `obtain ⟨r,hr⟩ := hprod cfg.threshold`. So the "liveness oracle" mostly *re-packages its own premise*. Honestly labeled (FLP forbids unconditional liveness), but it is a thin oracle. |
| `votersFor_length_mono` (:182), `quorum_monotone` (:208), `committedByQuorum_mono` (:223) | **GENUINE** | real `Nodup`/sublist/dedup monotonicity. Substantive. |
| `quorum_intersection_safety` (:308) | **GENUINE (strong)** | real inclusion-exclusion pigeonhole (`2·halfQuorum > n+f ≥ |Q₁∪Q₂|`). Honestly scopes out the contradiction step (needs the honesty model — closed in `BFT.lean`). |
| `liveness_after_gst` (:355) | **PORTAL** | discharged from the `gst_liveness` field. As thin as that field. |
| `world_no_downgrade` (:273) | **GENUINE** | relays `Finality.no_downgrade`. |

### `Proof/BFT.lean` — BFT safety + liveness reduction

| theorem | verdict | why |
|---|---|---|
| `honest_witness_in_intersection` (:121), `bft_safety` (:174), `bft_agreement` (:186) | **GENUINE (the consensus crown jewel)** | real Malkhi–Reiter: inclusion-exclusion gives `|Q₁∩Q₂| > f`, the `≤f` Byzantine filter leaves a *non-empty honest* intersection, `honest_vote_once` then contradicts conflict. The `BFTModel` fields are honest hypotheses (fault bound, `n>3f`, honest-vote-once), and `Inhabited.model` (:212) witnesses them at `n=4,f=1`. This is the strongest distributed result in the corpus. |
| `gst_liveness_from_round_model` (:288) | **GENUINE (thin) / PORTAL-feeding** | `GSTRound` (:275) is **defined as** `cfg.threshold ≤ (votersFor …).length` — i.e. **the quorum conclusion itself**. So "GSTRound ⇒ committedByQuorum" is `unfold`-then-`exact hgst`. The "liveness" theorem is a definitional restatement: the GSTRound hypothesis *is* the quorum. |
| `gstRound_of_productivity` (:316) | **GENUINE (thin)** | `obtain ⟨r,hr⟩ := hprod cfg.threshold` — re-packages the productivity premise. |

### `Proof/BFTLiveness.lean` — the pacemaker

| theorem | verdict | why |
|---|---|---|
| `Pacemaker` class | **PORTAL (the load-bearing illusion)** | `responsive_quorum : ∀ r, gst ≤ r → cfg.threshold ≤ (votersFor (votesOf (recv r)) (block r)).length` — this field **directly asserts the quorum forms**. It IS the GSTRound conclusion modulo the leader's block. |
| `gstRound_obtains` (:146) | **VACUOUS-as-liveness** | `obtain ⟨r,_,hgst⟩ := P.synchronizes P.gst; exact P.responsive_quorum r hgst`. Both inputs are hypothesis fields; `responsive_quorum` *is* the conclusion. So "a GST round obtains" is **assumed twice over** (the round exists by `synchronizes`, the quorum forms by `responsive_quorum`). No protocol content. |
| `liveness_of_pacemaker` (:162), `gst_liveness_of_pacemaker` (:187) | **PORTAL** | composition of two assumed fields. "World.gst_liveness is DERIVED" means "derived from a field that assumes the same thing". Honestly named (the OPEN at :254 admits the synchronizer *construction* is the real residue), but the "reduction" moves the assumption, it does not discharge it. |
| `Inhabited.pacemaker` (:235) | **DEGENERATE WITNESS** | leader always proposes block 7; `ref_quorum_at` holds because the fixed schedule delivers 3 voters. Inhabits the structure but with the quorum hand-delivered. |

### `Proof/Synchronizer.lean` — the geometric expected-O(1) bound

| theorem | verdict | why |
|---|---|---|
| `expected_failures_eq`/`expected_views_eq`/`expected_views_O1`/`honest_hit_as` (:87-125) | **GENUINE (real mathlib analysis)** | genuine `tsum_coe_mul_geometric_of_norm_lt_one` / `tsum_geometric_of_abs_lt_one` — `E[views]=1/h≤3/2` and the geometric law sums to 1. Real probability. |
| `synchronizer_round_obtains` (:212) | **VACUOUS-as-descent (the disconnect)** | takes `hhit : ∃ r, max t gst ≤ r ∧ honestLeader r` as a **hypothesis** and unpacks it. The genuine `honest_hit_as` (sum=1) is **NEVER USED** to produce the index — the §5 OPEN admits the a.s.→index bridge is missing. So the real math and the consensus descent are **disconnected**: the analysis proves a number, the descent assumes the hit. |
| `synchronizes_skeleton` (:224) | **VACUOUS (drops the content)** | proves only `∀ t, ∃ r, t ≤ r ∧ gst ≤ r` via `r := max t gst` — a trivial arithmetic fact carrying **no honest-leader content**. "discharges the `Pacemaker.synchronizes` skeleton" by dropping the load-bearing part. |

### `Proof/BeaconSpace.lean` (+ `BeaconSpaceInterior.lean`)

| theorem | verdict | why |
|---|---|---|
| `noHonestEverGe_measure_zero` (:203), `honestLeader_ae(_ge)` (:227), `honestLeader_index_exists(_ge)` (:253) | **GENUINE (real measure theory)** | genuine `tendsto_measure_iInter_atTop` (continuity-from-above) ∘ `(1-h)^N → 0`. The a.s.→constructive-index bridge `Synchronizer` lacked, actually built. |
| `BeaconSpace.indep_block` field | **PORTAL** | the per-view Bernoulli independence is a carried field — the entire probabilistic content is assumed. |
| `BeaconSpace.Inhabited.beacon` (:335) | **DEGENERATE** but **RESCUED by `BeaconSpaceInterior`** | the BeaconSpace-file witness is `dirac(allHonest)` at `h=1` (independence trivially `0^N`). **BUT** `BeaconSpaceInterior.lean` supplies a *genuine* interior witness: `Measure.infinitePi (bernoulli 3/4)` discharging `indep_block` with **real cross-view independence** (`interior_indep_block`, :109). So the worry I'd flag is **closed** — the abstraction is non-vacuously instantiable at a real interior `h`. Credit where due. |
| `synchronizer_round_obtains_over_beacon` (:299) | **GENUINE (within the beacon) / feeds the portal** | reads `honestLeader` off the witnessing stream and discharges `hhit`. Real *given the measure*. But it produces an honest *leader*, which `responsive_quorum` then turns into a quorum **by assumption** (see `BFTLiveness`). |

### `Proof/CoinductiveAdversary.lean`

| theorem | verdict | why |
|---|---|---|
| `rel_traj_of_bisim` (:142), `obsBisim_traj_of_bisim` (:166), `obsStream_eq_of_bisim` (:194) | **GENUINE (coinduction) / hypothesis-routed** | real native-coinductive corecursion over `νF`. BUT each takes `IsBisim Impl Spec R` as a **hypothesis** — the bisimulation relating Impl to the oracle is *given*, never built. Recall `Boundary.Later := Q` (identity), so the "▶-guarded" lift is unguarded. |
| `stepComplete_carries_infinite` (:227) | **GENUINE** | real `stepComplete_preserves` over `run_traj`. The safety face is solid. |
| `obsBisim_refl` (:262), `safe_fragment_iconfluent` (:253) | **WEAK / TAUTOLOGY** | the only proven non-vacuity is **reflexivity** (`bisim_eq`); the safe fragment is `Confluence.top_iconfluent` (`fun _ => True`). So "confluence-up-to-bisimulation" is *inhabited only by the diagonal and the trivial invariant*. |
| `obsBisim_of_uptoComm` (:436) + Paco §8 | **GENUINE (machinery) / hypothesis-routed** | the `gpaco`/`commClo` up-to-closure is real Paco machinery, fully proved. BUT it derives `ObsBisim` from a *bisimulation-up-to-closure `R` supplied as a hypothesis* — the "general case (derive the relation)" still takes the relation. The §7/§8 prose claims the residue is "CLOSED"; in fact the *up-to principle* is closed, but the *relation for the real system* is still an input. |

### `Proof/ContendedCrossCell.lean` — the contention dichotomy

| theorem | verdict | why |
|---|---|---|
| `applyHalfOut_bal_frame`/`_frame`/`debitFires_frame_disjoint`/`applyHalfOut_comm_disjoint` (:138-180) | **GENUINE (strong)** | real **general** (∀ `bt`) frame + commutation lemmas on the executable kernel. Not `decide`-over-a-toy. |
| `contended_commits_confluent` (:249) | **GENUINE (crown jewel)** | real schedule-agnostic confluence of disjoint debits, off the commutation lemma. The coordination-free safe fragment, actually proved. |
| `coupled_schedules_disagree` (:359), `coupled_no_schedule_agnostic_commit` (:381) | **GENUINE (the impossibility)** | `decide`-checked over a concrete pot that the two schedules commit differently, then a real `¬∃` that no schedule-agnostic verdict exists. The CAP/BEC obstruction as a theorem. |
| `disjoint_is_iconfluent_fragment` (:296) | **WEAK** | `:= top_iconfluent` (`fun _ => True`) — the bridge to I-confluence is via the *trivial* invariant, not the actual disjoint-debit invariant. The real content is the operational theorems; this bridge is thin. |
| `coupled_is_nonconfluent_must_escalate` (:407), `dichotomy_nonvacuous` (:424) | **GENUINE** | real `cardLeOne_not_iconfluent` + `nonpairwise_escalation` + the concrete coupled example outside the safe fragment. |

### `Proof/CrossCellLTS.lean` + `Proof/ForestLTS.lean`

| theorem | verdict | why |
|---|---|---|
| `crossAbsStep_forward` (:207), `crossAbsRun_forward` (:279) | **GENUINE** | real bilateral forward-sim square; (C5) joint conservation DERIVED on the machine (shared `amt`), (A)/(G) from real `caps`-frame + grounding lemmas. |
| `crossAbsStep_not_vacuous` (:304) | **GENUINE (negative)** | exhibits a turn for which the step FAILS (ungrounded over empty graph) — the grounding conjunct does real work. |
| `half_breaks_per_cell_conservation` (:336), `cross_conservation_is_not_per_cell` (:353) | **GENUINE (the obstruction)** | real machine-checked proof that per-cell conservation is FALSE of a bilateral half — the cross-cell measure is irreducible. Substantive. |
| `crossAbsStep_bound` (:382), `crossAbsStep_needs_binding` (:394) | **GENUINE** | the CG-2 binding is a load-bearing hypothesis; the negative reuses `JointCell.binding_is_proper`. |
| `forestApply_cg5_conserves` (:259), `forestAbsStep_forward` (:306), `forestAbsRun_forward` (:377) | **GENUINE (N-ary)** | real `Finset.sum` telescoping (`sum_sub_distrib`) generalizing the bilateral; the Σ=0 binding is a load-bearing hypothesis. `forestAbsStep_needs_binding` (:426) exhibits a non-summing family. |
| `biToForest_balanced` (:453), `forestAbsStep_two_refines_crossAbs` (:474) | **GENUINE** | the bilateral case really falls out as the `Fin 2` slice. |

### `Proof/WPCatalog.lean` — the userspace verification loop

| theorem | verdict | why |
|---|---|---|
| `ledgerSM_eq_expected` (:91) | **TAUTOLOGY (`rfl`)** | the eDSL elaborates to the expected term — definitional, but a meaningful no-codegen-gap check. |
| `ledger_VC_preserve` (:218), `ledgerCounter_VC_preserve` (:256) | **GENUINE (automation)** | closed by the fail-loud `vcg_discharge`; the conservation + monotone-counter VCs are real (the `#eval`/`decide` discriminating tests at §7 confirm the gate admits the good move, rejects 3 violations). |
| `ledger_run_sound` (:232), `ledgerCounter_run_sound` (:267) | **GENUINE (capstone)** | real `vcg_run_sound` over `inducedSystem recordCell`. End-to-end eDSL→run-invariant. |
| §6 honesty-rail `fail_if_success` negatives | **GENUINE** | the tactic provably cannot fake-close (badSpec). |

---

## 2. The complete vacuity list (file:line)

**A. `= rfl` / `Iff.rfl` definitional tautologies (proposition unfolds to the hypothesis):**
- `Finality.conservation_tier_independent` (`Finality.lean:335`) — `rfl` over a discarded `Tier` arg (self-flagged as a repair, still `x=x`).
- `CryptoKernel.discharged_iff_verify` (`CryptoKernel.lean:75`) — `Iff.rfl`.
- `Authority.Predicate.discharged_iff_registryVerify` (`Predicate.lean:93`), `registry_sound` (:106), `registry_sound_find` (:118) — `Iff.rfl`/`:= haccept`; "soundness-by-verification" = "accept = accept".
- `Authority.Caveat.token_discharges` (`Caveat.lean:142`) — `:= h`.
- `WPCatalog.ledgerSM_eq_expected` (`WPCatalog.lean:91`) — `rfl` (benign codegen-gap check).

**B. Re-projection theorems (conclusion is a repackaging of the hypothesis):**
- `Blocklace.equivocation_detectable` (`Blocklace.lean:198`) — `⟨⟨a,b,e⟩, e.incomp⟩`.
- `Blocklace.observer_detects` (`Blocklace.lean:210`) — `⟨e, hsee.1, hsee.2⟩`.
- `BFT.gst_liveness_from_round_model` (`BFT.lean:288`) — `GSTRound` IS the quorum conclusion.
- `BFT.gstRound_of_productivity` (`BFT.lean:316`), `World.liveness_after_gst` (`World.lean:355`) — re-package `hprod`/the oracle field.

**C. PORTAL bodies (theorem body = a hypothesis/structure FIELD; only model is trivial):**
- `Privacy.unlinkable` (:395), `zkauthchain_sound` (:405), `blinded_membership_hides_element` (:416), `nullifier_hides_identity` (:451) — the whole graph privacy tier; `graphRef` sets every carrier `True`.
- `BFTLiveness.gstRound_obtains` (`BFTLiveness.lean:146`), `liveness_of_pacemaker` (:162), `gst_liveness_of_pacemaker` (:187) — `Pacemaker.responsive_quorum` IS the quorum.
- `World.gst_liveness` field (`World.lean:115`) + `liveness_after_gst` (:355).
- `Laws.search_sound` (:60) — honest §0 portal.

**D. Disconnected genuine math (real theorem proven, never wired to the consensus claim it advertises):**
- `Synchronizer.honest_hit_as`/`expected_views_O1` (`Synchronizer.lean:113/125`) — real, but `synchronizer_round_obtains` (:212) takes the hit `hhit` as a hypothesis instead of deriving it from the a.s. result; the §5 OPEN admits the a.s.→index bridge is missing in-file (it IS built in `BeaconSpace`, but `Synchronizer`'s own descent doesn't use its own theorem).
- `Synchronizer.synchronizes_skeleton` (:224) — proves only the trivial arithmetic, drops honest-leader content.

**E. Weak-only non-vacuity (the greatest fixpoint / safe fragment is inhabited only by the diagonal / the trivial `True` invariant):**
- `Boundary.sound_refl` (:211) — reflexivity only.
- `CoinductiveAdversary.obsBisim_refl` (:262), `safe_fragment_iconfluent` (:253) — diagonal + `fun _ => True`.
- `ContendedCrossCell.disjoint_is_iconfluent_fragment` (:296), `CoinductiveAdversary.safe_fragment_iconfluent` — bridge via `top_iconfluent`, not the actual invariant.

**F. Degenerate types in load-bearing spots:**
- `Boundary.Later Q := Q` (`Boundary.lean:103`) — the `▶` "later" guard is the **identity**; every "▶-guarded" claim downstream (`IsBisim.step_rel`, `CoinductiveAdversary`) is over an unguarded recursion. Productivity is asserted in prose, not modeled.

**G. Self-trivializing structure laws (true because the structure carries its own proof):**
- `Authority.Positional.lossy_attenuation_only` (`Positional.lean:203`) — `⟨m.in_le, m.out_le⟩` (the attenuation proofs are fields). Honest self-repair, but content-free as a *theorem*.
- `Resource.excl_no_dup` (`Resource.lean:185`) — true because `Excl.op` is *constantly* `invalid`, not specifically self-composition.
- `Resource.ConfinesAuthority := Fpu`, `Confluence.Tier1Eligible := IConfluent` — unifications by definition, not by proof.

No `sorry`/`axiom`/`native_decide` beyond the three by-design ones. Every vacuity is "true-but-empty" or "true-but-portal", not unsound.

---

## 3. Fidelity findings (Lean vs the Rust)

| mechanism | Lean | Rust anchor (per docstrings) | verdict |
|---|---|---|---|
| **caveat / biscuit / macaroon** | `Caveat.Token` = root + append-only caveat chain; `attenuate_narrows` | `turn/src/action.rs:422 Authorization::Token`, macaroon HMAC / biscuit Ed25519 | **FAITHFUL.** The narrowing is real and the biscuit/macaroon cross-vat split is modeled (`crossVatVerifiable`). |
| **CDT attenuation** | `Finset Auth ⊆` over `DerivationPath` | seL4 CDT `Mint`/`Copy`/`Revoke` | **FAITHFUL** on the rights-lattice shape (real `⊆`, unlike the this-session `ExecRights=Unit`). The `CapHash` injectivity is honestly a §8 obligation. |
| **blocklace equivocation** | `precedes` transitive closure, `Equivocation`/`Equivocator` | `blocklace/finality.rs` `EquivocationProof`, `detect_equivocation` | **FAITHFUL** as a semantic DAG fact; `signed`/`id` crypto honestly §8. (Caveat: `equivocation_detectable` re-projects, so the "detection" content is in the *demo*, not the general theorem.) |
| **predicate registry** | `Registry = WitnessedKind → Option Verifier`, dispatch + fail-closed | `cell/src/predicate.rs:206/489/844 WitnessedPredicateRegistry` | **FAITHFUL** on dispatch; `registry_sound` is a tautology but `adversarial_find_cannot_forge` is the real soundness. |
| **credential revocation** | revocation set = nullifier G-Set, `revoke_blocks_verify` | `credentials/`, non-membership negative discharge | **FAITHFUL.** Reuses the real monotone nullifier invariant. |
| **value commitment** | `commit_hom` homomorphism, `committed_iff_cleartext` | `cell/value_commitment.rs` Pedersen/Ristretto | **FAITHFUL on the algebra**, honest §8 range-proof gap (`RangeObligation`). The Reference `commit := +` is a toy but labeled. |
| **BFT quorum** | `n>3f`, `n-f` quorum, honest-vote-once → `bft_safety` | Cordial-Miners / Malkhi–Reiter | **FAITHFUL** to the *classical BFT model*. ⚑ Note the MEMORY caveat: dregg1 actually runs Cordial-Miners DAG+Stingray, not classical BFT — so this is faithful to the *literature model*, and `Proof/CordialMiners.lean` (this-session) is what bridges to the DAG. |
| **consensus liveness** | `Pacemaker`/`responsive_quorum`/`gst_liveness` | DLS88/HotStuff/ELRS partial-synchrony | **SHADOW.** The genuine math (geometric, measure-0 tail) proves an honest leader is *eventually elected*; the step "honest leader ⇒ quorum delivered" (`responsive_quorum`) is **assumed**, not derived. Faithful to the *spec* of a synchronizer; the *protocol* liveness is portal. The OPENs name this honestly. |
| **cross-cell / forest conservation** | `joint`/`forest` CG-5 via shared-`amt` / Σ=0 binding | `circuit::bilateral_aggregation_air` CG-2/CG-5 | **FAITHFUL.** The half-edge cancellation is real; CG-2 binding honestly a hypothesis. |

**Net fidelity:** the authority/token/CDT/blocklace/credential/value-commitment layers are
**faithful** to their Rust anchors (and use real lattices — a marked improvement over the
executable layer's Unit collapse). The **consensus *liveness*** layer is a *spec-shaped shadow*:
honest about being assumed, but the protocol content is portal. The **privacy graph tier** is
portal-only.

---

## 4. Ranked de-vacuification target list

**Tier 1 — make a portal/disconnect genuine (the leverage points):**

1. **Wire `Synchronizer.honest_hit_as` to `synchronizer_round_obtains`.** The a.s.→index bridge
   EXISTS (`BeaconSpace.honestLeader_index_exists`), but `Synchronizer`'s own descent ignores its
   own geometric theorem and takes `hhit` as a hypothesis. Route the descent through the BeaconSpace
   index so the geometric math is actually load-bearing for the consensus conclusion.

2. **`Pacemaker.responsive_quorum` → derive the quorum from the honest leader.** This single field
   *assumes the quorum forms*, collapsing `gstRound_obtains`/`liveness_of_pacemaker` to portals.
   Model HotStuff's "honest leader + Δ-delivery ⇒ honest supermajority votes are counted" as a
   *theorem* over `World.recv` + the honesty model, instead of a field. This is the genuine
   remaining consensus-liveness research (honestly OPEN), but it is THE load-bearing gap.

3. **`Privacy` graph tier — give `graphRef` a non-trivial witness.** Every stealth/anonymity/
   blinded-membership theorem is `True` in its only model. At minimum, exhibit a *non-degenerate*
   `GraphPrivacyKernel` where `Indistinguishable`/`UnlinkableToHolder` are not `fun _ => True`
   (e.g. an information-theoretic toy where two distinct addresses genuinely map to equal views),
   so the parametric theorems are non-vacuous in a model that isn't constant-`True`.

**Tier 2 — strengthen weak-but-genuine results:**

4. **`CoinductiveAdversary` / `Boundary` — make `Later` a real guard** (or drop the productivity
   prose). `Later Q := Q` means the coinductive story is unguarded. Either model `▶` over a
   step-index (the `Resource.lean` header already proposes reusing the camera's `▶`), or stop
   claiming productivity the identity-`Later` does not provide. And: build a *non-reflexive*
   `ObsBisim` witness (relate Impl to a genuinely-different Spec), since `obsBisim_refl` is the only
   inhabitant.

5. **`ContendedCrossCell.disjoint_is_iconfluent_fragment` → bridge to the ACTUAL disjoint-debit
   invariant**, not `top_iconfluent` (`fun _ => True`). The operational theorems are genuine; the
   I-confluence bridge currently routes through the trivial invariant.

6. **`Blocklace.equivocation_detectable` / `observer_detects` — strengthen past re-projection.**
   State detection as a *decidable procedure* over the lace that *returns* the witnessing pair from
   the raw blocks (the `demo_detect` shape generalized), not a theorem that takes the equivocation
   as input.

**Tier 3 — tautology cleanups (cosmetic but over-claimed):**

7. **`Finality.conservation_tier_independent`** — already self-flagged; either delete it (the
   genuine content is `conservedAtTier_holds`) or restate the orthogonality non-trivially.

8. **`Predicate.registry_sound` / `CryptoKernel.discharged_iff_verify` / `Caveat.token_discharges`**
   — these `Iff.rfl` "keystones" should be demoted in prose from "THE KEYSTONE" to "definitional
   unfolding"; the real soundness is `adversarial_find_cannot_forge`.

---

## 5. Honest bottom line

Counting the ~230 theorems across the pre-session core corpus (excluding `#eval`/`example`
non-vacuity checks and the by-design sorries):

- **GENUINE and fidelity-faithful: ≈ 62%.** The whole `Execution` run-algebra; `Core`'s
  conservation corollaries + `withholding_no_free_copy`; the entire **authority spine** (`CDT`
  `path_attenuates` over a real `Finset` lattice, `Caveat` `attenuate_narrows`, `Discharge`
  monotonicity, `Credential` revocation, `Blocklace` `honest_no_equivocation`/`cdt_is_blocklace`/
  `attested_mono`); `Resource`'s three cameras (all laws proved, docstring stale); `Spec.Conservation`
  (`committed_iff_cleartext` genuinely consumes injectivity); `Privacy`'s field + value tiers;
  `World`'s quorum monotonicity + `quorum_intersection_safety`; **`BFT.bft_safety`** (real
  Malkhi–Reiter counting); the **executor/cross-cell crown jewels** (`ContendedCrossCell`
  confluence + impossibility, `CrossCellLTS`/`ForestLTS` forward-sim squares + non-composition
  obstruction, `WPCatalog` end-to-end); and the genuine analysis in `Synchronizer`/`BeaconSpace`.

- **PORTAL (honest carried assumption, NOT a proof): ≈ 18%.** The entire `Privacy` **graph tier**
  (stealth/anonymity/blinded-membership — `True` in its only model); the consensus **liveness**
  chain (`Pacemaker.responsive_quorum` + `gstRound_obtains`/`liveness_of_pacemaker`,
  `World.gst_liveness`); `Laws.search_sound`. These are kernel-clean and honestly labeled, but
  prove *nothing about the system* beyond "the interface is inhabitable".

- **TAUTOLOGY / re-projection (true-but-empty): ≈ 12%.** The `Iff.rfl` "soundness-by-verification"
  family (`registry_sound`, `discharged_iff_verify`, `token_discharges`),
  `Finality.conservation_tier_independent`, `Blocklace.equivocation_detectable`/`observer_detects`,
  `BFT.gst_liveness_from_round_model` (GSTRound = the quorum), `synchronizes_skeleton`.

- **WEAK-only non-vacuity (inhabited only by diagonal / trivial invariant): ≈ 8%.** `sound_refl`,
  `obsBisim_refl`, the `top_iconfluent`-routed safe-fragment bridges.

**Two systemic illusions inflate apparent coverage:**

1. **The consensus-liveness tower.** A genuinely impressive stack of analysis (geometric
   expected-O(1) views, measure-0 no-honest-leader-ever, the interior Bernoulli product) sits atop
   a foundation (`responsive_quorum`) that **assumes the very quorum it claims to deliver**. The
   math is real; the descent to "the protocol is live" is portal. `Synchronizer`'s own descent
   doesn't even use its own geometric theorem. The OPENs are honest about it, but a reader sees
   `liveness_of_pacemaker : ∃ r block, committedByQuorum …` and "0 sorries" and over-reads it.

2. **The "soundness-by-verification" tautology family.** `registry_sound`/`discharged_iff_verify`/
   `token_discharges` are advertised as keystones but are `Iff.rfl` (accept = accept). The genuine
   soundness (the prover cannot forge) lives in `adversarial_find_cannot_forge` and `find_untrusted`.

**The good news that the prior audit's framing would not predict:** unlike the this-session
executable layer (`ExecRights := Unit`), the pre-session authority/resource spine is built on
**real lattices** (`Finset Auth ⊆`, `List Auth`, the `Auth` camera) and proves **real**
attenuation, BFT safety, and cross-cell confluence/impossibility. The single highest-leverage fix
is **#2 above** (derive the quorum from the honest leader), which would convert the entire
consensus-liveness portal stack into a genuine result and make the (already-genuine)
`Synchronizer`/`BeaconSpace` analysis load-bearing. The single most over-claimed item is the
**`Privacy` graph tier**, whose every theorem is `True` in its only model.
