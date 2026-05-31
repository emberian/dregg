# dregg2 Consistency Surface — the full trusted-assumption carrier audit

**Scope.** This enumerates EVERY Prop-carrying typeclass field, every structure-field
hypothesis carrying a proof obligation, and the three by-design `sorry`s in
`/Users/ember/dev/breadstuffs/metatheory/Dregg2/`. For each carrier it states the carried
Prop (file:line), classifies it CRYPTO-STANDARD vs SYSTEM-LEVEL, and locates its consistency
witness — tagged:

- **NON-TRIVIAL-PROVED** — an axiom-clean (`#print axioms` ⊆ {propext, Classical.choice,
  Quot.sound}), *discriminating* instance: the witness REJECTS a dishonest input, so the
  conditioned theorems are not vacuous. (Model citizen: `VatBoundary.phi_functorial_concrete`.)
- **TRIVIAL-ONLY** — the only witness is `fun _ => True` / `Unit` / Verify-always-true. The
  conditioned theorem is consistent but VACUOUS. (Vacuity risk; two already killed:
  GraphPrivacyKernel-all-True, ExecRights=Unit.)
- **MISSING** — no inhabiting instance found (possible vacuity, must investigate).
- **CRYPTO-STANDARD** — a bare `Prop` carrier for a hardness assumption (collisionHard,
  binding, extractable, unforgeable, …) that is NECESSARILY Lean-trivial to discharge (you
  cannot prove DLog-hardness in Lean). HONEST; isolated; NOT the vacuity risk.

**What this proves / does NOT prove.** This audit establishes CONSISTENCY + NON-VACUITY (a
non-trivial model satisfying the system-level Props exists), NOT FAITHFULNESS to real dregg or
real crypto (the separate Rust-grounding axis). The crypto Props are flagged and held apart
from system-level carriers throughout.

**Verification.** Every file cited below was compiled standalone with
`lake env lean FILE` (REAL exit captured, not head/tail-masked); all = `REAL=0`. Witness
axiom-cleanliness confirmed via the in-file `#assert_axioms` / `#print axioms` pins
(e.g. `DesignatedVerifier.lean` `#print axioms` showed the keystones depend on
`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`).

---

## A. The three by-design `sorry`s

| # | Carrier (Prop) | file:line | Class | Witness / discharge | Tag |
|---|---|---|---|---|---|
| S1 | `Core.conservation_step` — `cons.count A + minted f.tag = count B + burned f.tag` (the per-turn balance equality) | `Dregg2/Core.lean:154-162` | SYSTEM-LEVEL | **`Exec.conservation_step_realized` PROVED** (`Dregg2/Exec/StepComplete.lean:91-93`, = `(cexec_attests h).1`), `#assert_axioms`-clean (`Dregg2/Claims.lean:46`). The abstract obligation IS discharged for the executable kernel `cexec`; the three Core corollaries (`conservation_ordinary/_minted/_burned`, `Core.lean:166+`) are PROVED FROM it. | **NON-TRIVIAL-PROVED** (interface obligation, realized) |
| S2 | `Laws.search_sound` — `Searchable.find p = some w → Discharged p w` (untrusted prover soundness-by-verification) | `Dregg2/Laws.lean:53-60` | SYSTEM-LEVEL (interface contract on an external opaque oracle) | By design irreducible in-module: `find` is opaque with no in-module relation to `Verify`. **Recovered at the consumer** where `find`'s output is RE-CHECKED by `Verify`: `Authority/Intent.lean:122-123` (`resolve` re-runs `Verify`, so no appeal to the contract is needed) and `Authority/Predicate.lean:113` (`registry_sound_find`). | **NON-TRIVIAL-PROVED** (contract; obviated at every real consumer by re-verification) |
| S3 | `Spec.VatBoundary.phi_functorial` — the three `PhiFunctorial` laws over an ARBITRARY `Verifiable` | `Dregg2/Spec/VatBoundary.lean:359-401` | SYSTEM-LEVEL | **`phi_functorial_concrete` PROVED, axiom-clean** (`VatBoundary.lean:441-456`, `#assert_axioms` at :456). A DISCRIMINATING verifier (`Verify s b := b`, accepts `true`, REJECTS `false` — not Verify-always-true) with a maximally-lossy `stmtOf`. The abstract `sorry` is INTENTIONALLY omitted from the tripwires (`VatBoundary.lean:462-463`) because over an arbitrary `Verifiable` `preserves_id` needs an accepting witness to exist (false at `Verify ≡ false`). | **NON-TRIVIAL-PROVED** (the model citizen; abstract form stays honestly OPEN) |

All three are isolated: the abstract `sorry` never silently flows into a "proved" keystone
(S1 realized + corollaries proved-from; S3's abstract is excluded from `#assert_axioms` while
its concrete witness is pinned).

---

## B. SYSTEM-LEVEL carriers (the genuine vacuity surface)

These carriers shape the SYSTEM behaviour (privacy, consensus, cross-cell binding, authority).
A trivial witness here WOULD leave conditioned theorems vacuous — this is exactly where the
worry lives.

| Carrier | Prop carried | file:line | Witness (file:line) | Tag |
|---|---|---|---|---|
| `GraphPrivacyKernel` (class; fields `unlinkable_law`, `stealth_k_anonymity`, `zkauthchain_law`, `nullifier_hides_law` + `k_gt_one : 1 < k`) | view-equality hiding on a CONCRETE `addrView`/`nullifierView : … → Nat` + `≥ k > 1` anonymity sets — NOT an abstract relation | `Dregg2/Privacy.lean:375-415` | **`Reference.graphRef`** (`Privacy.lean:585-621`): `addrView a := a.oneTimeKey % 2` is GENUINELY NON-CONSTANT (`example` at :657 proves `addrView ⟨0⟩ ≠ addrView ⟨1⟩`); real 2-element `Finset` anonymity sets; `k := 2`. A `def` (not auto-instance) so it cannot silently satisfy a real obligation. `#assert_axioms unlinkable …` clean (:679-688). | **NON-TRIVIAL-PROVED** (the previously-killed all-True version is gone) |
| `BlindedMembershipKernel Elem` (class; `hides_law`, `member_k_anonymity` + `k_gt_one`) | view-equality hiding on concrete `memberView : Elem → SetCommitment → Nat` + `≥ k > 1` member sets | `Dregg2/Privacy.lean:422-443` | **`Reference.memRefNat`** (`Privacy.lean:627-641`): `memberOf e _ := e < 2` is a GENUINE predicate (`example` at :669 proves `2` is NOT a member); real `{0,1}` anonymity set; `k := 2`. | **NON-TRIVIAL-PROVED** |
| `World Msg` (class; laws `recv_mono`, `gst_liveness`) | network monotonicity + the GST/partial-synchrony progress oracle (conditioned on the honest-quorum/`hprod` premise) | `Dregg2/World.lean:76-126` | **`World.Reference` instance** (`World.lean:387-409`): `recv r := fixedVotes.take r` — a real append-only schedule; `recv_mono` proved via `take_sublist`; `gst_liveness` discharged from `hprod` honestly (relays the precondition, supplies no unconditional liveness — FLP-respecting). `example` at :413 computes a real quorum. | **NON-TRIVIAL-PROVED** (`recv_mono` real; `gst_liveness` premise-conditioned, honest) |
| `BFTModel cfg votes` (structure; fields `fault_bound`, `bft_threshold`, `population_bound`, `honest_vote_once`) | the `n>3f` BFT floor + `≤f` adversary budget + honest-vote-once honesty law | `Dregg2/Proof/BFT.lean:79-98` | **`Inhabited.model`** (`BFT.lean:212-237`): `n=4,f=1` (minimal `3f+1`), three honest voters, empty adversary; `honest_vote_once` proved because no voter double-votes. `bft_safety`/`bft_agreement` apply to it (`example` :241). `#assert_axioms` clean (:350-352). | **NON-TRIVIAL-PROVED** |
| `Pacemaker Msg votesOf cfg` (structure; fields `synchronizes` carrying `honestLeader r`, `honest_quorum`, `honest_le_delivered`) | DLS88 GST + ELRS honest-leader synchronization + BFT supermajority + HotStuff responsive *delivery* — the conclusion-in-disguise `responsive_quorum` was REMOVED | `Dregg2/Proof/BFTLiveness.lean:117-143` | **`Inhabited.pacemaker`** (`BFTLiveness.lean:253-260`) over `World.Reference`: GST=3, honest leader at every view, 3 honest endorsers, delivery proved by `ref_delivered_at` (:238). `gstRound_obtains`/`gst_liveness_of_pacemaker` apply (`example` :264,:268). `#assert_axioms` clean (:313-315). | **NON-TRIVIAL-PROVED** (the assumed-quorum portal killed; quorum now DERIVED from delivery) |
| `SuperRatification S cfg l` (structure; fields `votes_for_l`, `quorum`, `unique_leader`) | the DAG-BFT `≥ n−f` ratifying quorum + `leader_blocks.len()==1` anchor uniqueness | `Dregg2/Proof/CordialMiners.lean:263-273` | **`SuperRatification.ofLace` PROVED** (`CordialMiners.lean:288-304`): the `votes`/`quorum` are CONSTRUCTED FROM THE REAL LACE (`ratifyingVoters`, count derived via `length_votersFor_votesFromVoters_of_nodup` from `quorum_from_lace`), not assumed structure data. `committed_to_superRatification` (:311). | **NON-TRIVIAL-PROVED** (derived from the lace, not hypothesized) |
| `Hyperedge ι T turnId halfEdge` (structure; the apex CG-2 ⊗ CG-5 binding) | the wide-pullback turn-binding (shared `tid` + Σ-zero half-edges) | `Dregg2/Hyperedge.lean:80` | **`ringHyperedge` PROVED** (`Hyperedge.lean:273`, real `N`-cycle over ℤ, Σ=0) + **`hyper_binding_is_proper` PROVED** (`Hyperedge.lean:164`): a singleton config that is NOT `HyperAdmissible` (CG-5 `1≠0`) — the binding is a PROPER subobject, hence genuine content. | **NON-TRIVIAL-PROVED** (proper-subobject witness; not vacuous) |
| `JointBinding` / `SharedTurnId` (structures; CG-2 turn-identity pullback ⊗ CG-5) | the binary cross-cell binding hypothesis consumed by `joint_sound`/`joint_stepComplete` | `Dregg2/JointTurn.lean:91, 134` | **`binding_is_proper` PROVED** (`JointTurn.lean:333-342`): a one-state coalgebra with half-edge `1` whose CG-5 `1+1≠0` makes the binding a non-trivial constraint — joint-admissible is a PROPER subset. `family_joint_sound` (:458) PROVED well-posed. | **NON-TRIVIAL-PROVED** |
| `MacKernel Key Bytes Tag` (class; field `unforgeable : Prop`) — STRUCTURAL integrity part | the chain-integrity theorems (`verify_iff_wellTagged`, `integrity_tail_binds`, `forgery_requires_mac_query`, `removal_breaks_tail`) | `Dregg2/Authority/CaveatChain.lean:78-87` | The integrity theorems are PROVED over an ABSTRACT `mac` and do NOT consume `unforgeable` (`CaveatChain.lean:165-285`). **`Demo` instance** `mac k m := 31*k+7*m+1` (:380) is DISCRIMINATING: `forgedDropped.verify = false`, `forgedTampered.verify = false` (`#eval` :413,:419). | **NON-TRIVIAL-PROVED** (structural integrity; `unforgeable` itself is crypto — see §C) |
| `DVKernel Verifier Statement Proof VSecret` (class; field-LAW `simulate_verifies`) | a verifier's own simulated transcript verifies under it (deniability core); + the `Transferable`/`DesignatedFor` dial | `Dregg2/Authority/DesignatedVerifier.lean:84-103` | **`Reference` instance** (`DesignatedVerifier.lean:303-307`) is DISCRIMINATING: `v0` accepts its own simulated tag (`example` :318) but `vOther` REJECTS it (`example` :325 — the teeth). `designated_not_transferable`/`dial_endpoints_distinct` `#print axioms` clean. | **NON-TRIVIAL-PROVED** (discriminating, model-citizen-shaped) |
| `HolderAnonymity Digest` (class; field-LAW `hides_law` whose CONCLUSION is the ABSTRACT relation `ViewIndistinguishable : Nat → Nat → Prop`) | two authorized members of one issuer root have indistinguishable blinded views | `Dregg2/Crypto/BlindedSet.lean:137-155` | **`Reference.anonKernel`** (`BlindedSet.lean:409-413`): `view := fun _ _ => 0`, **`ViewIndistinguishable := fun _ _ => True`**, `hides_law := trivial`. The premise (`MemberOf`) IS non-trivial, but the law's CONCLUSION predicate is abstract and the ONLY witness collapses it to `True`. | **⚠ TRIVIAL-ONLY** (structurally identical to the killed all-True GraphPrivacyKernel; the conclusion-side carrier `ViewIndistinguishable` has no discriminating witness) |

**System-level count:** 11 carriers. **NON-TRIVIAL-PROVED: 10.** **TRIVIAL-ONLY: 1**
(`HolderAnonymity.ViewIndistinguishable`). **MISSING: 0.**

---

## C. CRYPTO-STANDARD carriers (necessarily Lean-trivial — HONEST, isolated)

Bare `Prop` carriers for cryptographic hardness / external-oracle facts. You cannot prove
these in Lean (DLog-hardness, FRI soundness, foreign-chain finality), so a `True` discharge in
the reference instance is CORRECT and EXPECTED. They are consumed as explicit hypotheses by
the theorems that use them (parametric), never silently. **These are NOT the vacuity risk** —
but note (below) where one INTERACTS with a system-level theorem.

| Carrier | file:line | Reference discharge | Real discharge |
|---|---|---|---|
| `CryptoKernel.collisionHard` | `Dregg2/CryptoKernel.lean:61` | `True` (`CryptoKernel.lean:131`) | Poseidon2/BLAKE3 CR |
| `CryptoPrimitives.collisionHard` / `binding` / `unlinkable` | `Dregg2/Crypto/Primitives.lean:50,58,64` | `True` (`Primitives.lean:101,…`) | Poseidon2 CR / Pedersen-DLog / anonymity advantage |
| `PedersenVerifierKernel.extractable` / `binding` | `Dregg2/Crypto/Pedersen.lean:305,308` | `True` (`Pedersen.lean:526-527`) | STARK FRI+Fiat-Shamir / DLog binding |
| `MerkleVerifierKernel.extractable` | `Dregg2/Crypto/VerifierKernel.lean:53` | `True` (`VerifierKernel.lean:88+`) | STARK soundness |
| `DfaVerifierKernel.extractable` | `Dregg2/Crypto/Dfa.lean:209` | reference OPEN-noted (:417,:427) | STARK soundness |
| `TemporalVerifierKernel.extractable` | `Dregg2/Crypto/Temporal.lean:174` | — | STARK soundness |
| `BridgeVerifierKernel.extractable` | `Dregg2/Crypto/Bridge.lean:222` | — | STARK soundness + digest binding |
| `BlindedSetVerifierKernel.extractable` | `Dregg2/Crypto/BlindedSet.lean:195` | `True` (`BlindedSet.lean:368`) | STARK + compress-CR |
| `NonMembershipVerifierKernel.extractable` | `Dregg2/Crypto/NonMembership.lean:275` | — | STARK + compress-CR |
| `CustomVerifierKernel.extractable` (parametric over registered `vk`) | `Dregg2/Crypto/Custom.lean:147` | toy `vk` registered (:31) | app circuit STARK soundness |
| `MacKernel.unforgeable` | `Dregg2/Authority/CaveatChain.lean:87` | `True` (`CaveatChain.lean:381`) | HMAC-SHA256 unforgeability |
| `DischargeCrypto.cryptoSound` (+ proved law `unseal_seal`) | `Dregg2/Authority/ThirdPartyDischarge.lean:90` | **`False`** in `refCrypto` (`ThirdPartyDischarge.lean:372`) — HONESTLY records "toy is not sound"; law statements never depend on it | XChaCha20-Poly1305 / HMAC / SHA256 |
| `ProofForest.ProofNode.StepProofValid` (the per-node STARK-verify Prop) + `ProofForest.attested` (the §8 portal entered as DATA) | `Dregg2/Exec/ProofForest.lean:98, 119` | parametric; composition theorem (`§3`) proved over `attested`'s output | `verify_effect_vm(proof, pi) = true` |
| `EffectsSupply.ForeignFinal` (`opaque … : Prop`) | `Dregg2/Exec/EffectsSupply.lean:105` | opaque (no witness needed — external) | foreign-chain (Cardano) finality via observation bridge |
| `UCBridge.FComDischarge` fields `correct` / `perfectHiding` / `bindingReducesToDLog` | `Dregg2/Crypto/UCBridge.lean:92,95,99` | bundled `_holds` proof fields + `entails_binding`/`entails_unlinkable` (`UCBridge.lean:100+`) — a `Type`-level DATA structure, NOT an axiom; the CryptHOL `Dregg2_FCom.thy` proofs are the witnesses; `binding_discharged_by_crypthol`/`unlinkable_discharged_by_crypthol` PROVED kernel-clean | CryptHOL `pedersen.*` theorems (cross-system) |

**Crypto-standard count:** ~15 carriers (8 `extractable` + 3 primitive + collisionHard +
unforgeable + cryptoSound + StepProofValid + ForeignFinal + 3 FComDischarge). All correctly
Lean-trivial / external; UCBridge is special — it carries its own CryptHOL-proof witnesses and
entailments rather than a `True`.

---

## D. Carriers that INTERACT (could a conjunction jointly contradict / jointly vacuate?)

A consistency witness for each carrier in ISOLATION is necessary but not sufficient: a joint
instance over the SAME types could be unsatisfiable (vacuity) or derive `False`
(contradiction). The interactions:

1. **`World` ⊗ `BFTModel` ⊗ `Pacemaker`** (all over `Msg = Vote`, `votesFor`/`Finality.Config`).
   These are co-instantiated: `BFTLiveness.Inhabited.pacemaker` is built `open
   Dregg2.World.Reference` over the SAME `World.Reference` instance, and `BFT.Inhabited.model`
   uses a compatible config. **JOINTLY WITNESSED, axiom-clean** — the `n=4,f=1` / `n=3,f=0`
   configs and the `fixedVotes` schedule satisfy `recv_mono` + `gst_liveness` + the BFT floor
   + honest-vote-once + the pacemaker delivery simultaneously. No contradiction: safety
   (`bft_safety`) and liveness (`gst_liveness_of_pacemaker`) hold of the SAME reference world.
   The one subtlety — could `bft_safety` (which derives `False` from two conflicting quorums)
   make the model vacuous? No: it derives `False` only from the EXTRA premise `b₁ ≠ b₂ ∧` both
   reach `n−f`; the inhabiting `votes` has a single block, so the antecedent is never met. The
   `False`-conclusion is the intended safety contradiction, not a model inconsistency.

2. **`BFTModel` ⊗ `SuperRatification`** (CordialMiners `cordial_agreement`). The DAG-BFT safety
   theorem consumes a `BFTModel` over the COMBINED ratification votes plus two
   `SuperRatification`s. `SuperRatification.ofLace` derives both from a real lace, and the BFT
   feeder is the same `Inhabited.model` shape. **JOINTLY CONSISTENT** — the quorum-intersection
   core is transferred verbatim; no field of one contradicts the other.

3. **`CryptoKernel` ⊗ `Verifiable` seam ⊗ `search_sound`.** `verifiableOfCryptoKernel`
   (`CryptoKernel.lean:70`) makes `CryptoKernel.verify` the `Laws.Verify`. The `search_sound`
   (S2) contract is about `Searchable.find`, a SEPARATE opaque oracle; no algebraic relation
   forces them to agree, so no contradiction — and the reference `CryptoKernel` (verify = echo,
   `CryptoKernel.lean:127`) is DISCRIMINATING (rejects non-matching proofs), inhabiting the
   seam non-vacuously.

4. **`HolderAnonymity` ⊗ `BlindedSetVerifierKernel`** (both over the same `Digest`, both in
   `BlindedSet.lean`). The verifier-kernel side (`extractable`, soundness) is CRYPTO-STANDARD
   and discriminating-witnessed (`refKernel` rejects non-`root=3` statements). The anonymity
   side (`HolderAnonymity`) is the TRIVIAL-ONLY carrier. They do not contradict (one is about
   soundness, the other hiding), but the anonymity CONCLUSION (`ViewIndistinguishable`) remains
   vacuous regardless of the sound co-instance — flagged below.

5. **`UCBridge.FComDischarge` → `CryptoPrimitives.binding`/`unlinkable`.** The bridge structure
   ENTAILS the two primitive crypto carriers (`entails_binding`, `entails_unlinkable`). This is
   a one-directional discharge (crypto ⇒ crypto), not a system-level interaction; consistent
   because `FComDischarge` is inhabitable as `Type`-data carrying the CryptHOL proofs.

No pair derives `False`; no pair is jointly unsatisfiable. The only joint-vacuity residue is
isolated to interaction (4), entirely on the TRIVIAL-ONLY `HolderAnonymity` conclusion.

---

## E. Verdict and the single actionable finding

**The system is NOT vacuous and NOT contradictory** at the system level. Of 11 system-level
carriers, **10 are NON-TRIVIAL-PROVED with axiom-clean discriminating witnesses** (the two
previously-caught traps — all-True GraphPrivacyKernel, ExecRights=Unit — are confirmed dead;
GraphPrivacyKernel now has a non-constant `addrView`, and the rights/consensus carriers are now
DERIVED from real data: `SuperRatification.ofLace`, the lace, the delivered-vote count, the
proper-subobject bindings). The three by-design `sorry`s are isolated and each has a
proved/realized counterpart (S1 realized in the executor, S2 obviated by re-verification at
consumers, S3 the model-citizen concrete witness). The ~15 crypto-standard carriers are
honestly Lean-trivial and correctly isolated as explicit hypotheses; `DischargeCrypto.cryptoSound`
is even discharged with `False` to advertise toy-unsoundness without the laws ever depending on
it.

**THE ONE FINDING — a TRIVIAL-ONLY system-level carrier (vacuity risk):**

> **`HolderAnonymity.hides_law`'s conclusion `ViewIndistinguishable : Nat → Nat → Prop`**
> (`Dregg2/Crypto/BlindedSet.lean:144,148-150`) is an ABSTRACT relation whose ONLY witness
> (`Reference.anonKernel`, `BlindedSet.lean:412`) discharges it with `fun _ _ => True` (and
> `view := fun _ _ => 0`). This is the SAME shape as the already-killed all-True
> GraphPrivacyKernel: the law's premise (`MemberOf`) is genuine, but its conclusion predicate
> is abstract and the theorem `blindedset_hides_holder` (`BlindedSet.lean:158-161`) therefore
> says only `True` at the sole witness — VACUOUS in the hiding content.
>
> **Antidote (matches the GraphPrivacyKernel fix that was applied in `Privacy.lean`):** replace
> the abstract `ViewIndistinguishable` carrier with a CONCRETE view-equality conclusion
> (`view m root = view m' root` over a genuinely NON-CONSTANT `view`), exactly as
> `Privacy.BlindedMembershipKernel.memberView`/`hides_law` already do (`Privacy.lean:432-438`,
> witnessed non-trivially by `memRefNat`). The `Privacy.lean` sibling proves this is achievable
> axiom-clean; `BlindedSet.HolderAnonymity` is the one place the older abstract-relation idiom
> survived.

Everything else on the trusted-assumption surface is either a proved non-trivial system witness
or an honest, isolated crypto-standard hardness assumption.

---

## F. VERDICT — independent adversarial re-audit (READ-ONLY, default-skeptical)

This section is an INDEPENDENT second pass that tried to BREAK the consistency + non-vacuity
claim, not to confirm it. Every machine fact below was re-derived from source (not the table
above). Method: standalone `lake env lean FILE` with REAL exit captured (not head/tail-masked),
plus a full `lake build Dregg2.Consistency Dregg2.Claims` (REAL=0, 3455 jobs).

### Machine-checked ground facts (re-verified, not cited)
- `Dregg2/Consistency.lean` compiles **REAL=0**; `#print axioms dregg_consistent_nonempty` =
  `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`, no fresh axiom**.
- `Dregg2/Claims.lean` compiles **REAL=0** and emits ~40 `#assert_namespace_axioms` pins
  (1000+ theorems across `Exec.*`, `Proof.*`, `Crypto.*`, `Authority.*`, `Paco`, …) all
  reporting "pinned kernel-clean". `#assert_namespace_axioms` **hard-fails the build** on any
  `sorryAx` dependency, so a REAL=0 here is machine-checked sorry-freedom for the whole proved
  corpus.
- Full `lake build` of the two targets: **REAL=0, 3455 jobs**. The ONLY `sorry` warnings in the
  entire build path are the two by-design ones reachable from these targets —
  `Core.lean:154` (S1) and `Laws.lean:53` (S2). S3 (`VatBoundary.phi_functorial`) is the third,
  documented and excluded from its module's pins. **No other `sorry` anywhere.** Remaining
  warnings are cosmetic (unused-variable, namespace-duplication lint, simp/simpa) — not soundness.
- `BFT.lean`, `BFTLiveness.lean`, `CordialMiners.lean`, `StepComplete.lean`, `Caps.lean` each
  compile standalone **REAL=0**, no `sorry`/`error`.

### Attack (1) — CONTRADICTION HUNT: **PASS** (no break found)
Tried to derive `False` from the conjunction of carriers, focusing on the task-named interacting
pairs:
- **Conservation ⊗ mint/burn/no-free-copy** (`Core.lean`). `withholding_no_free_copy` forces
  `count A = 0` ONLY for a cell `A` that admits an *ordinary* copy turn `A ⟶ A ⊗ A` over a
  *cancellative* monoid — a guarded conclusion, not a global collapse. The realized executor
  (`conservation_step_realized = (cexec_attests h).1`, `StepComplete.lean:91`) discharges the
  balance equality as a THEOREM about `cexec`, pinned kernel-clean in `Claims.lean`; the abstract
  `sorry` (S1) never flows into it. No `False`.
- **BFT `n>3f` ⊗ honest-vote-once ⊗ fault_bound** (`BFT.lean`). `bft_safety` concludes `False`
  by design, but ONLY from the EXTRA premise `b₁ ≠ b₂` ∧ two `n−f` quorums. The inhabiting
  `Inhabited.model` (`votes = [⟨0,7⟩,⟨1,7⟩,⟨2,7⟩]`, `n=4 f=1`, so `n−f=3`) gives a quorum ONLY
  for block 7; no second distinct block reaches a quorum, so the antecedent is never met and the
  model is consistent. The `False` is the intended safety contradiction, NOT a model
  inconsistency. The `BFTModel` structure type-checks as inhabited (the `model` def compiles), so
  the fields are jointly satisfiable.
- **Authority non-amplification ⊗ delegation** (`AuthModes.lean`, `Caps.lean`).
  `captp_granted_le_held` extracts `granted.rights ≤ held.rights` from the admission gate
  (`h.1.1`); over the REAL lattice `ExecAuth := Finset Auth` (7 distinct `Auth` values, 2^7
  elements, `≤` = `⊆`) this REJECTS an amplifying handoff. No contradiction with the delegation
  laws (`attenuate_subset`/`derive_no_amplify_rights` PROVED over the same lattice).
- **World ⊗ BFTModel ⊗ Pacemaker** (`Consistency.lean` cluster A). Liveness
  (`gst_liveness_of_pacemaker`) and safety (`bft_agreement`) hold of the SAME reference world in
  one Lean context (`cluster_network_bft_pacemaker_consistent`, pinned). `gst_liveness` is
  honestly premise-conditioned on `hprod` (FLP-respecting — a silencing adversary never supplies
  it), so no unconditional-liveness contradiction.
No pair, and no carrier-plus-proved-theorem, derived `False`. The joint record `SystemModel` is
inhabited (`dregg_consistent_nonempty`), which is itself the machine-checked proof that the
conjunction does not entail `False`.

### Attack (2) — TRIVIAL-WITNESS HUNT: **PASS** (the one flagged case is closed; re-examined ones hold)
- The surface's single TRIVIAL-ONLY finding — `HolderAnonymity.ViewIndistinguishable` discharged
  by `anonKernel` as `view ≡ 0`, `ViewIndistinguishable ≡ True` (`BlindedSet.lean:409-413`,
  re-read and confirmed it IS the all-True shape) — is **closed** in `Consistency.lean` by
  `discriminatingAnon` (`view _ root := root.toNat`, `ViewIndistinguishable := Eq`). Re-examined
  adversarially: `view` ignores the member (correct holder-anonymity semantics — hides *which*
  member) but is NON-CONSTANT in the public root (TOOTH 2: `view _ 3 ≠ view _ 5` by `decide`), and
  `Eq` over a non-constant view is FALSIFIABLE (distinct roots ⇒ distinct views ⇒ `¬ Eq`), so it
  does NOT secretly collapse to `True`. This is structurally the accepted `GraphPrivacyKernel`
  fix idiom. NOT a trivial witness.
- Re-examined the NON-TRIVIAL witnesses for a hidden collapse:
  - `phi_functorial_concrete` (model citizen): `Verify s b := b` rejects `false`;
    `lossy_on_confinement` EXHIBITS two distinct caps `⟨true,()⟩ ≠ ⟨false,()⟩` collapsing to one
    demand — a genuine non-injectivity witness. The `Rights := Unit` here is a verifier-functor
    parameter, NOT the killed `ExecRights=Unit` authority carrier (distinct concern; the authority
    rights live over `ExecAuth`). Discriminates.
  - `graphRef`: `addrView a := a.oneTimeKey % 2` non-constant (TOOTH `addrView ⟨0⟩ ≠ ⟨1⟩`); the
    `stealth_k_anonymity` Finset has genuine card-2 sets. `memRefNat`: `memberOf e _ := e < 2`,
    `2` is provably NOT a member. Both discriminate.
  - `SuperRatification.ofLace`: `votes`/`quorum` CONSTRUCTED from the real lace
    (`votesFromVoters (ratifyingVoters …)`, quorum via `length_votersFor_votesFromVoters_of_nodup`
    from `quorum_from_lace`) — inhabited ONLY when the lace exhibits ≥ n−f ratifiers; not
    hypothesized data.
  - `CryptoKernel.Reference`: echo-verifier accepts `7,7`, rejects `7,8` (both by `decide`).
  - `Hyperedge`/`JointBinding`: `hyper_binding_is_proper`/`binding_is_proper` PROVED — a product
    config is EXCLUDED by CG-5, so the binding is a proper subobject (genuine content).
No system-level carrier is dischargeable ONLY by a degenerate witness.

### Attack (3) — VACUOUS-CONDITIONING: **PASS** (main soundness-theorem hypotheses are falsifiable)
- `bft_safety` / `bft_agreement`: hypothesis "two distinct blocks each reach `n−f`" is FALSIFIABLE
  (single-block votes fail it) — and satisfiable by an equivocating/Byzantine assignment, so the
  theorem has content.
- `World.gst_liveness` / `gst_liveness_of_pacemaker`: premise `hprod` is FALSIFIABLE (a bounded
  or silencing delivery schedule fails it) — honest conditional liveness, not always-true.
- `captp_granted_le_held`: hypothesis `authModeAdmits (.capTpDelivered …)` is FALSIFIABLE over
  `ExecAuth` (an amplifying `granted ⊄ held` makes `decide (granted ≤ held)` false ⇒ no admission).
- `SuperRatification`/`Committed`: `Committed` is `Nonempty (superRatifiedFromLace …)` — FALSE for
  a lace with no super-ratifying quorum, so `cordial_agreement` is non-vacuously conditioned.
- `conservation_step_realized`: states `total s'.kernel = total s.kernel` along `cexec` —
  falsifiable in principle (a non-conserving step would break it); PROVED for `cexec`, so genuine.
Every main soundness theorem's hypothesis admits a falsifying assignment.

### Crypto-standard isolation (re-confirmed, NOT counted as non-vacuity evidence)
The ~15 bare-`Prop` hardness carriers (`collisionHard`, `binding`, `extractable`, `unforgeable`,
`StepProofValid`, `ForeignFinal`, FComDischarge, …) are necessarily Lean-trivial (you cannot
prove DLog-hardness in Lean) and are consumed as EXPLICIT hypotheses, never silently. They are
honest and held apart. `DischargeCrypto.cryptoSound` is even discharged `False` to advertise
toy-unsoundness without any law depending on it. These are the FAITHFULNESS axis, not the
vacuity axis — flagged, not conflated.

### Honest bottom line
After attacking on all three axes — contradiction, trivial-witness, vacuous-conditioning — and
re-deriving every machine fact from source (REAL=0 on `Consistency.lean` + `Claims.lean`; full
`lake build` REAL=0 over 3455 jobs; only the three by-design `sorry`s present; capstone
axiom-clean), **I could not find a break.** dregg2 is, on the evidence exhibited, **CONSISTENT
(no `False` derivable) and NON-VACUOUS (a discriminating, axiom-clean model inhabits every
system-level carrier simultaneously, `dregg_consistent_nonempty`)**, modulo the isolated
crypto-standard hardness assumptions (the honest, necessary Lean-trivial seam, separate from the
vacuity question). The single prior TRIVIAL-ONLY finding (`HolderAnonymity`) is the one closed by
`Consistency.lean`'s `discriminatingAnon`.

Per the default-skeptical standard: this is a **could-not-break-after-trying-(1)/(2)/(3)** PASS —
a non-trivial model PROVABLY exists and the conjunction PROVABLY does not entail `False` (the
`#print axioms`-clean `dregg_consistent_nonempty` IS that proof), but consistency beyond the
exhibited model is not claimed. No contradiction and no residual system-level vacuity to fix were
found.
