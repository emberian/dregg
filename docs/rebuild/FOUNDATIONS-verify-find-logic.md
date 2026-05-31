# FOUNDATIONS — the verify/find seam as an adjunction, and the proof-forest as a gluing

> **Lens (cand-B).** Read dregg2's categorical foundations through ONE seam — `verify ⊣ find` —
> and ONE composition — the **proof-forest** (per-node validity × `Linked` ⇒ whole-run
> `StepInv`) as a colimit/gluing. The question throughout: is the categorical vocabulary
> **load-bearing** (a universal property actually PROVED in the Lean) or **decorative**
> (suggestive notation buying no theorem) or **aspirational** (claimed by the design but
> standing on a `sorry`)? Every claim is tagged and grounded at `file:line`.
>
> **Read-only excavation. No code was changed.** Sources: `study-category.md`,
> `cand-{A,B,C}.md`, `REORIENT.md`, `GLOSSARY.md`, `pdfs/STUDY-lean4-coinduction.md`,
> `DREGG4-{HYPERSYSTEM,UNIFICATION}.md`, `CARRY-FORWARD-SYNTHESIS.md`, and the actual Lean in
> `metatheory/Dregg2/` (`Boundary`, `Core`, `Laws`, `Confluence`, `Finality`, `JointTurn`,
> `Hyperedge`, `Authority/{Positional,Predicate,CaveatChain,DesignatedVerifier}`,
> `Spec/VatBoundary`, `CryptoKernel`, `Proof/CoinductiveAdversary`, `Exec/{ProofForest,
> CrossCellForest}`).

---

## 0. TL;DR — what the lens found

The biggest single finding is that **two of cand-B's load-bearing slogans were caught false
in the Lean and corrected, without losing the soundness content**:

1. The headline of `study-category.md` — *"`νF₁ ⊗ νF₂` is not the final coalgebra"*
   (`tensor_non_finality`) — is **FALSE as stated** (the product of two final coalgebras IS
   final for the product functor). The Lean (`JointTurn.lean:322`) says so explicitly and
   replaces it with the TRUE fact: `binding_is_proper` — the joint-admissible configurations
   are a **proper equalizer subobject** of the product carrier. The architectural consequence
   the doc wanted (cross-cell soundness ≠ per-cell ∧ per-cell, the binding is an irreducible
   hypothesis) **survives intact** — it just rests on the proper-subobject fact, not on a
   non-finality that does not hold. **This is the single most important REAL/DECORATIVE
   correction.**

2. `Boundary.sound_of_step_complete` (the cand-A/-B "keystone" bisimulation-to-spec) was
   **FALSE as stated** (free `Spec`, refuted via `Spec.Carrier = Empty`) and was **removed**
   (`Boundary.lean:156–213`). The honest soundness-from-step-completeness content lives, PROVED,
   in `stepComplete_preserves` (a safety invariant along the whole execution), and the genuine
   coinductive bisimulation now lives — also PROVED — in `Proof/CoinductiveAdversary.lean`.

On the lens's own two objects:

- **The verify/find seam IS a real adjunction** — but it is `verify`, not `find`, that carries
  the universal property. `Laws.predicate_witness_galois` (`Laws.lean:101`) is a genuine,
  fully-PROVED Galois connection (the Birkhoff polarity of the `Discharged` relation). `find`'s
  side (`search_sound`, `Laws.lean:53`) is a **by-design `sorry`**: a *contract on an untrusted
  plugin*, never an in-Lean theorem. So "`find ⊣ verify`" as a literal adjunction-between-the-
  two-maps is **DECORATIVE**; the *real* adjunction is the predicate⊣witness polarity, and the
  asymmetry (decidable `Bool` verify / `Option` undecidable find) is baked into the **types**.

- **The proof-forest IS a real gluing** — `ProofForest.proofForest_sound` (`ProofForest.lean:177`)
  is PROVED: per-node validity (the §8 crypto seam, an explicit hypothesis) **×** `Linked` (a
  combinatorial chain-link) ⇒ whole-forest `StepInv`. It is a *finite* gluing/colimit-shaped
  composition (a 1-categorical sheaf-condition: local sections agreeing on overlaps glue). The
  **∞-colimit** (folding the whole history into one badge — the private-folding idea) is
  **ASPIRATIONAL**: explicitly NOT built (`ProofForest.lean:1–15`, "dregg has never had a sound
  proof aggregation"), and the architecture ships O(n) standalone proofs precisely because the
  O(1) recursive fold is a *deferred performance swap that provably does not touch soundness*.

- **§8 portal discipline ("the law never learns a secret") is a REAL structural separation.**
  `CryptoKernel`/`MacKernel`/`DVKernel` carry crypto soundness as **`Prop`-carriers**
  (`collisionHard`, `unforgeable`, `simulate_verifies`) — assumptions of the *correct kind*,
  never proved in Lean. `Verify P w : Bool` is a decidable oracle; the bisimulation/forest
  theorems are *parametric over* the kernel and never see binding/extractability.

---

## 1. The verify/find seam as an adjunction

### 1.1 The claim, and "appeared four independent ways"

`REORIENT §2` (B-law) and `cand-B §1` make the seam the spine of the whole system: TCB = the
*verifier*; every *search* (match a fill, find a delegation path, a handler, an order, "is this
cell dead") is undecidable and must be an untrusted plugin emitting a checkable witness; every
*gate* is cheap to VERIFY. The slogan is that this "appeared four independent ways" — auth-path
search, intent-match, ordering, schema-migration — all reducing to the same find/verify
asymmetry. `cand-B §1` then names the categorical content: *"`Verify` is the right adjoint
(cheap, decidable, posetal); `Find` is the left adjoint shadow (intractable)."*

### 1.2 What is actually PROVED — the predicate⊣witness Galois connection `[REAL]`

`Laws.lean` carries a genuine, fully-discharged adjunction — but it is **not** literally
`find ⊣ verify` between the two maps. It is the **Birkhoff polarity** of the verifier relation:

- `polarity_galois` (`Laws.lean:75`) — **PROVED, no hypotheses**: every relation `R : α → β → Prop`
  induces a monotone `GaloisConnection` between `Set α` and `(Set β)ᵒᵈ` via the upper/lower
  polars. This is the standard formal-concept / Birkhoff-dual adjunction. **Substantive: a real
  universal property (`l A ≤ B ↔ A ≤ u B`) actually proved.**
- `predicate_witness_galois` (`Laws.lean:101`) — **PROVED**: instantiates `polarity_galois` at
  the relation `Discharged p w := (Verify p w = true)`. The two preorders are *pinned concretely*
  — predicates ordered as `Set P` under entailment, witness-sets as `(Set W)ᵒᵈ` under
  specificity. The docstring is honest that this *replaces a prior placeholder that quantified
  over arbitrary `l, u` and "was false as stated"* (`Laws.lean:99`). The faithfulness audit
  agrees: `polarity_galois`/`predicate_witness_galois` are tagged **GENUINE** at
  `FAITHFULNESS-AUDIT-CORE.md:120–121`.
- `predicate_heyting` (`Laws.lean:111`) — **PROVED** (`= le_himp_iff.symm`): the predicate algebra
  is Heyting, so the residual `⇨` is exactly **attenuation** (a stricter predicate entails a laxer
  one). `study-category §3` is right that this threads coherently from `Laws` → admissibility →
  `Authority` attenuation. The `Authority.CaveatChain.append_narrows` (`CaveatChain.lean:223`,
  PROVED) and `Spec.VatBoundary.phi_composes_with_attenuation` (`VatBoundary.lean:314`, PROVED)
  are the same `≤`-narrowing discipline cashed out cryptographically.

**Verdict.** The adjunction is REAL — but its content is the **predicate⊣witness polarity**, and
it is `verify` (the relation `Discharged`) that *generates* it. The Galois pair is between
predicate-sets and witness-sets, not between the two *functions* `find` and `verify`.

### 1.3 What `find ⊣ verify` literally is — DECORATIVE, by design `[DECORATIVE]`

The literal reading "`find` is the left adjoint of `verify`" buys no theorem and is not even
stated as one. `find` is `Searchable.find : P → Option W` (`Laws.lean:48`), and its only contract
is `search_sound` (`Laws.lean:53`): *if* `find p = some w` *then* `Discharged p w`. That theorem's
body is a **`sorry`** with an explicit, correct justification (`Laws.lean:54–60`):

> "PRIMITIVE: `Searchable.find` is an opaque oracle (the prover/matcher plugin).
> Soundness-by-verification is a *contract* on that external plugin; there is no relation between
> the typeclass's `find` and `Verify` in-module to derive it from."

The faithfulness audit tags this **BY-DESIGN OK / PORTAL-OK** (`FAITHFULNESS-AUDIT-CORE.md:39,119`):
the honest content lives in `Authority/Predicate.lean`, NOT in deriving `search_sound`. So:

- To be a *real* adjunction `find ⊣ verify`, dregg would have to prove a unit/counit pair — at
  minimum `p ≤ verify(find p)` and `find(verify w) ≤ w` in the appropriate orders, i.e. that
  `find` is the *best* (left-universal) witness-producer. **It proves none of this, and
  cannot** — `find` is undecidable, so there is no universal left adjoint to exhibit (that is
  precisely the point of the seam). The asymmetry is encoded structurally instead: `verify`
  returns `Bool` (decidable, total, the right-adjoint/posetal side), `find` returns `Option`
  (partial, no completeness, no termination). **The types ARE the "adjunction"; the word is
  decoration over a deliberate non-theorem.**

This is not a defect — it is `cand-B`'s thesis stated correctly: *soundness is by verification,
never by construction*. The lens's contribution is to name it precisely: **`verify` carries a
real Galois adjunction (predicate⊣witness); `find` carries a contract, not an adjoint.**

### 1.4 The genuine teeth on the find side — `[REAL]`

The honest content the `search_sound` `sorry` defers is PROVED in `Authority/Predicate.lean`:

- `find_untrusted` (`Predicate.lean:138`) — **PROVED `∃`**: there is a registry, statement, and
  prover returning `none` while a discharging witness exists. So "the prover found nothing" can
  NEVER be read as "no witness exists" — *completeness is not on the table, by construction.*
- `adversarial_find_cannot_forge` (`Predicate.lean:151`) — **PROVED**: for *every* prover `find`
  and *any* witness it synthesizes, if the honest verifier rejects `(stmt, wit)` then the
  registry dispatch rejects. The prover is fully quantified over and **never appears in the
  conclusion** — the gate is the sole authority.

This is the real categorical content of the seam: the verifier is a *retract* the untrusted
search cannot subvert. The find side is forced to be sound *through* the verifier, which is
exactly soundness-by-verification, proved against an adversarial `find`.

### 1.5 The badge = (permitted ∧ committed), NOT a grant of standing `[REAL — definitional]`

`GLOSSARY.md:153–159` pins the badge as the `Obs` artifact a turn returns across a vat boundary,
attesting **(permitted) ∧ (effects-as-committed)** — a legal derivation existed (de-jure) *and*
the committed effects are real — and explicitly **not a grant of standing** (de-facto authority
is recovered from the log, the Miller `BA`-vs-`TP` split). This is faithfully carried in the
Lean:

- `Authority.Positional.Integrity` (`Positional.lean:132`) is the *admissibility* relation
  (intra trivial / cross `Discharged`), not an authority-conferral. `boundary_law`
  (`Positional.lean:152`, PROVED) admits a change iff `owner ∈ subjects ∨ ∃ w, Discharged …` —
  permission, not standing.
- `confinement_preserved` (`Positional.lean:170`, PROVED) and `PasRefined` (`Positional.lean:96`)
  encode "the policy is an upper bound; authority never grows" — the de-jure/permission spine,
  with de-facto recovered behaviorally (the log), exactly as the badge definition requires.
- The cleanest single statement that the badge is *not* standing: `Spec.VatBoundary.phi_drops_
  confinement` (`VatBoundary.lean:202`, PROVED) — **permission survives the crossing, authority
  does not.** A crossed cap can be *presented* (permission) but admits only under a discriminating
  far-side `Verify` (authority is now the far side's to revoke). This is the badge's `(permitted)`
  half made into a theorem and *separated* from standing.

---

## 2. The §8 portal discipline — "the law never learns a secret"

### 2.1 The structural separation is REAL `[REAL]`

`cand-A §8`, `cand-B §3.3`, `REORIENT §6`, and the `dregg2 §8` README all demand: **crypto
soundness is NEVER merged into the Lean law.** `Verify P w : Bool` is a decidable oracle; its
binding/extractability is a *circuit* obligation. The Lean implements this as **Prop-carriers**
on portal classes — the correct *kind* of assumption (a `Prop` "no PPT adversary…", not an
idealized total function):

- `Crypto.CryptoKernel` (`CryptoKernel.lean:40`): `verify : Digest → Proof → Bool` is opaque;
  `collisionHard : Prop` (`CryptoKernel.lean:61`) is the carrier — the docstring even narrates the
  prior `hash_inj : Injective` being a *KIND error* (real Poseidon is collision-resistant, not
  injective) and fixing it to a `Prop`. The one genuinely-algebraic law, `commit_hom`
  (`CryptoKernel.lean:54`), is the Pedersen homomorphism — present because the metatheory *uses*
  it, and Pedersen satisfies it exactly.
- `Authority.CaveatChain.MacKernel` (`CaveatChain.lean:78`): `mac : Key → Bytes → Tag` opaque;
  `unforgeable : Prop` (`CaveatChain.lean:87`) the carrier. The integrity laws are stated as
  **reductions**: `forgery_requires_mac_query` (`CaveatChain.lean:305`, PROVED) shows a
  forged-but-accepted chain *exhibits a MAC collision* — "forge ⇒ break HMAC", with HMAC security
  left as the portal. dregg never claims to prove HMAC secure; it proves the reduction.
- `Authority.DV.DVKernel` (`DesignatedVerifier.lean:84`): the verifier-indexed `verifyFor` and the
  simulator `simulate`, with `simulate_verifies` (`DesignatedVerifier.lean:102`) the §8 law — a
  class field, *never* a Lean theorem.

**The portal IS the verify/find seam.** `verifiableOfCryptoKernel` (`CryptoKernel.lean:70`) makes a
`CryptoKernel` *instantiate* `Laws.Verifiable`; `discharged_iff_verify` (`CryptoKernel.lean:75`)
is definitional. So §1's `Discharged` and §2's portal are the *same* object viewed at two
altitudes — the abstract seam and its crypto realization.

### 2.2 "The law never learns a secret" as a theorem `[REAL]`

The sharpest evidence this is structural, not aspirational, is `Spec.VatBoundary`: the entire
named-loss story is PROVED *without the Lean ever seeing a key*. The verifier is just a
`Verifiable` instance; "discriminating" is the abstract hypothesis "`Verify` accepts some witness
and rejects some witness" (`VatBoundary.lean:202–215`). From that alone:
`phi_drops_confinement`, `forwarded_cap_is_revocable`, `revocable_iff_not_authority`
(`VatBoundary.lean:202,240,251`) are all PROVED, axiom-clean (`#assert_axioms`, `VatBoundary.lean:
465–474`). The law reasons about *what a verifier can decide*, never about secrets — exactly "the
law never learns a secret."

The `DesignatedVerifier` module is the proof that this separation has real expressive power: it
shows the *old* universal `Discharged` (no verifier index) **literally cannot express** "convincing
only to V" (`DesignatedVerifier.lean:15–19`), and the verifier-indexed generalization
`DischargedFor` (`DesignatedVerifier.lean:113`) recovers public mode as the `∀ V` collapse
(`publicMode_collapses_to_universal`) while making designated-verifier deniability provable
(`designated_is_deniable`). The semantic content (verifier-indexing, the simulator repudiation
argument) is PROVED; the crypto (DV-NIZK / chameleon) is the portal. Clean separation, both halves.

---

## 3. The proof-forest as a gluing / colimit / sheaf condition

### 3.1 The composition theorem is REAL `[REAL]`

`Exec/ProofForest.lean` packages the forest composition with the assumed/proved boundary made
explicit:

- `ProofNode` (`ProofForest.lean:81`) = the public-input projection of one cell-step
  (`oldCommit`/`newCommit`/`effectsHash`/`prevReceipt`/`seq`/`δ`) **plus** `StepProofValid : Prop`
  — the §8 seam carried as a hypothesis, never a concrete predicate.
- `Linked`/`chainLinked` (`ProofForest.lean:137,148`) = the **combinatorial chain-link** along
  every consecutive edge: `prev.newCommit = next.oldCommit` (state continuity) ∧
  `next.prevReceipt = prev.newCommit` (receipt pointer) ∧ `next.seq = prev.seq + 1`. Pure
  combinatorics over the PI vectors — no crypto.
- `ProofForest.attested` (`ProofForest.lean:124`) = the §8 portal entered as DATA: "if every
  node's proof verifies, the EffectVm AIR's soundness gives a real committed `execForest` run."
- `proofForest_sound` (`ProofForest.lean:177`) — **PROVED, axiom-clean** (`#assert_axioms`,
  `ProofForest.lean:223`): `(∀ n, StepProofValid) ∧ Linked ⇒ fullProofForestInv` (Conservation ∧
  Authority ∧ ChainLink ∧ ObsAdvance over the whole forest), reducing to `execForest_attests`.
- `proofForest_factors` (`ProofForest.lean:217`) states the §8 boundary as an explicit factoring:
  **per-node validity (ASSUMED, crypto) × `Linked` (PROVED, combinatorial) ⇒ whole-forest soundness.**

### 3.2 Is it a colimit / gluing / sheaf condition? `[REAL as a 1-categorical gluing; the universal property is DECORATIVE]`

The shape is exactly a **gluing / sheaf condition over a 1-category of cell-steps**, and the lens
endorses it as a faithful description — with one caveat about how much "colimit" is doing:

- **The sheaf reading is apt and grounded.** Think of the happened-before edges as a site: each
  `ProofNode` is a *local section* (a per-step `StepInv` witness valid on its own PI); `Linked` is
  the *agreement-on-overlaps* condition (the overlap of consecutive steps is the shared commitment,
  and `newCommit = oldCommit` is the restriction maps agreeing). `proofForest_sound` is the
  **gluing axiom**: locally-valid sections that agree on overlaps glue to one global section (the
  whole-run `StepInv`). The negative test confirms the sheaf condition *bites*: an UNLINKED list
  with each node individually valid is NOT `chainLinked` (`ProofForest.lean:293`, PROVED `¬`) —
  local validity alone does NOT glue; **the overlap-agreement is load-bearing**, which is exactly a
  sheaf condition's content (not a presheaf's). This is real, not decoration.
- **The cross-cell case is a wide-pullback gluing, also REAL.** `Exec/CrossCellForest.lean` does the
  cross-cell analogue: `crossForest_attests` (`CrossCellForest.lean:278`, PROVED) glues N cross-cell
  half-edges, where the overlap condition is the **CG-5 N-ary balance** `Σ δ = 0`
  (`crossForest_conserves`, `CrossCellForest.lean:241`). `crossForest_needs_binding`
  (`CrossCellForest.lean:319`, PROVED) shows the binding is a *genuine* restriction (a proper
  subobject) — i.e. the gluing is non-trivial, carving out a proper sub-family.
- **What is DECORATIVE:** calling `proofForest_sound` a *colimit* with a universal property. Nothing
  proves an initiality/terminality (no "the glued proof is universal among proofs agreeing on
  overlaps"). It is a *conjunction-glues-to-conjunction* fact (`fullForestInv` is literally the
  pointwise `StepInv` telescoped), which is the **equalizer/limit-flavored** sheaf gluing, not a
  colimit with a mapping-out universal property. The honest categorical word is **"the forest is the
  limit of its per-step sections over the linking diagram"** (a finite sheaf gluing), not "a
  colimit." The Lean proves the gluing equation; it does not prove a universal property, so the
  colimit framing buys no theorem.

### 3.3 The ∞-colimit (private folding into one badge) is ASPIRATIONAL `[ASPIRATIONAL]`

The lens-specific question: *does the proof-forest gluing extend to an ∞-colimit — folding the
whole history into one badge?* The Lean answer is explicit and honest:

- **NOT built, by design.** `ProofForest.lean:1–15` opens: *"dregg has never had a sound, useful
  proof AGGREGATION (compressing an interaction DAG into one succinct recursive proof — IVC /
  STARK-in-STARK / folding)… So the architecture does not compress. It ships the whole forest of
  per-step proofs… Cost: O(n) instead of O(1); aggregation slots in later as a pure performance
  swap that provably does not touch the soundness story."* `REORIENT §0/§2` and `cand-A §2.4`
  confirm: recursion is a *deferrable feature* behind a `RecursionBackend` trait, **depth = security
  parameter, no unconditional/arbitrary-depth IVC.**
- **Why it is ASPIRATIONAL, not merely deferred-engineering:** the ∞-fold would have to prove that
  the colimit of the whole (unbounded) history is itself a single verifiable badge whose soundness
  equals the conjunction of all per-step soundnesses. The closest the Lean comes is the *infinite*
  bisimulation in `Proof/CoinductiveAdversary.lean` — and that is genuinely PROVED, but it proves a
  *different* thing: that the running cell stays bisimilar to the oracle *forever* (the observation
  stream is schedule-robust, `obsStream_eq_of_bisim`, `CoinductiveAdversary.lean:194`), and that a
  step-complete cell carries `Good` along the *whole* trajectory (`stepComplete_carries_infinite`,
  `CoinductiveAdversary.lean:227`). That is the ∞-*behaviour* (a greatest-fixpoint over `νF`), NOT
  an ∞-*proof-fold-into-one-badge*. The badge-fold would need a recursive verifier whose O(1)
  output certifies the O(n) (or ω) history — exactly the deferred `RecursionBackend`. **So the
  ∞-colimit is ASPIRATIONAL: the design names it, the soundness story is explicitly arranged so it
  is a later swap, and no Lean theorem folds the history into one badge today.** The honest residue
  is even written into `ProofForest.lean:325–330` (`-- OPEN:` the cross-cell proof-forest fold).

> **Lens synthesis on the fold.** dregg2 has the *finite* gluing (sheaf condition over the linking
> diagram, PROVED) and the *infinite behaviour* (greatest-fixpoint bisimulation over `νF`, PROVED).
> The one thing it does **not** have — and deliberately defers — is the *infinite proof-object*: the
> ∞-colimit that compresses ω-many local proofs into a single succinct badge. The private-folding
> idea is exactly this missing ∞-colimit, and it is correctly tagged ASPIRATIONAL: the architecture
> is built so its absence costs only succinctness (O(n) verify), never soundness.

---

## 4. The three orthogonal judgements (conservation / ordering / I-confluence)

`REORIENT §2` and `study-choreography` insist on three *independent* judgements per turn. The Lean
realizes the orthogonality concretely and non-vacuously:

- **Conservation (Law 1, linear/SMC).** `Core.conservation_step` (`Core.lean:154`) is the one
  balance `sorry` (an operational obligation, honestly a `-- PRIMITIVE:`), from which
  `conservation_ordinary`/`mint_delta`/`burn_delta`/`withholding_no_free_copy`
  (`Core.lean:166,176,187,209`) are all **PROVED**. The "no free copy" (`Δ` withheld) is real
  (`left_eq_add.mp` over a cancellative monoid). **`[REAL]` for the monoid-hom + invariance.**
  `study-category §2` is right that the *"strong monoidal functor"* dressing is **DECORATIVE** —
  the Lean docstring itself says so (`Core.lean:11–13`: "the functor laws collapse to the monoid-hom
  + invariance"; target is discrete on objects). **`[DECORATIVE]` for "functor."**
- **I-confluence (the third judgement, BEC).** `Confluence.lean` — `IConfluent` (`Confluence.lean:44`),
  `Tier1Eligible` (`Confluence.lean:51`), and the *non-vacuity witnesses* `top_iconfluent`
  (`Confluence.lean:95`, PROVED) and `cardLeOne_not_iconfluent` (`Confluence.lean:104`, PROVED `¬`).
  `nonpairwise_escalation` (`Confluence.lean:70`, PROVED) gives the constructive clashing-pair. So
  "linear ⇏ I-confluent" is a *proved falsifiable distinction*, not prose. **`[REAL]`.**
- **Ordering / canonicity (Law 2, finality).** `Finality.lean` — `Tier` is a PROVED `LinearOrder`
  (`Finality.lean:96`), `rank_injective` (`Finality.lean:84`, PROVED). The genuine distributed-
  agreement obligations (the `committed`/quorum laws) are honest `Prop`-`sorry`s (`Finality.lean:
  34`: "each `sorry` is a real obligation"). **`[REAL]` for the tier lattice + no-downgrade
  shape; the consensus-agreement theorems themselves are partly `[ASPIRATIONAL]` (`sorry`'d
  obligations).**

The three are genuinely separate in the type structure: conservation lives in `Core`
(`AddCommMonoid`), I-confluence in `Confluence` (`SemilatticeSup`), ordering in `Finality`
(`LinearOrder` on `Tier`). They share no carrier, so the orthogonality is structural, not asserted.

---

## 5. The tensor binding — the corrected irreducibility `[REAL, after correction]`

This is the lens's headline correction (TL;DR #1), expanded.

`study-category §1` makes "the tensor non-finality" *"the single most important coherence-finding"*
— the place the category is load-bearing: cross-cell joint-soundness is irreducible to per-cell
soundness *precisely because* `νF₁ ⊗ νF₂` allegedly fails to be final. **The Lean found this
slogan false and corrected it** (`JointTurn.lean:319–346`):

> *"Correction (audit): the earlier `tensor_not_final` ('νF₁ ⊗ νF₂ is not final') was mis-stated —
> the product of two final coalgebras IS final for the product functor, so that claim is false. The
> true, soundness-critical content is a proper-subobject fact: `JointBinding` (CG-2 ⊗ CG-5) is a
> non-trivial constraint, so the joint-admissible configurations are a proper equalizer subobject of
> the product carrier."*

- `binding_is_proper` (`JointTurn.lean:333`) — **PROVED**: there exist two one-state cells whose
  CG-5 balance `1 + 1 = 2 ≠ 0` fails, so that product configuration is *not* `JointAdmissible`. The
  joint-admissible set is a **proper equalizer subobject**, so cross-cell admissibility is genuinely
  MORE than per-cell × per-cell — **the binding must be a hypothesis, never derived.** The
  architectural mandate of `study-category §1.4` (`joint_sound` takes the binding as a premise)
  **survives**, on a true foundation.
- The N-ary lift is PROVED too: `Hyperedge` (`Hyperedge.lean:80`) is the **wide pullback** (N-fold
  fiber product over `TurnId`) — CG-2 the cone (`Hyperedge.lean:92`), CG-5 one Σ-over-univ = 0
  (`Hyperedge.lean:99`). `hyperedge_sound` (`Hyperedge.lean:374`, PROVED, `#assert_axioms`) and
  `hyperedge_sound_needs_binding` (`Hyperedge.lean:409`, PROVED `¬`) close it; `legs_agree`
  (`Hyperedge.lean:111`, PROVED) collapses all N CG-2 legs into one theorem (no `O(N²)` pairwise
  gluing at the apex). **The wide-pullback framing is REAL and load-bearing** — it dissolves the
  agreement *bookkeeping* but **not** the binding-as-premise (the irreducible residue persists).

**Lens note.** This is the cleanest example of the doc's own discipline working: a categorical
slogan that *would have* papered over a missing/false theorem was caught, the false universal
property discarded, and the *true* universal property (a proper equalizer subobject = a real
limit/pullback) proved in its place. Tag the *binding-as-irreducible-hypothesis*: **REAL**. Tag the
*"⊗ of coalgebras is not final"* slogan: **DECORATIVE (and corrected — it was false)**.

---

## 6. INFINITY-CELL and HIGHER-ORDER cell / turn (the lens's answer)

Through the verify/find + gluing lens, here is the sharpest reading I can ground:

### 6.1 What a HIGHER-ORDER turn is `[REAL up to n; ASPIRATIONAL for the full simplicial object]`

A turn is a 1-cell (a coalgebra step `c : X → F X`). The **higher cells of the interaction
complex** are the n-ary atomic joint-turns:

- **2-cell** = a `JointTurn` (the binary atomic interaction; `SharedTurnId` CG-2 pullback +
  `JointBinding` CG-2 ⊗ CG-5). REAL: `JointTurn.lean:86,121`.
- **n-cell** = a `Hyperedge` over `Fin n` (the wide pullback). REAL and PROVED: `Hyperedge.lean:80`,
  `hyperedge_sound`. So **a higher-order turn = an n-ary atomic joint-turn whose filler carries its
  own CG-2 cone + CG-5 Σ=0 binding.**
- The slide to a *full simplicial object* (face/degeneracy maps, simplicial identities — an
  ∞-categorical interaction complex) is **ASPIRATIONAL**: `DREGG4-HYPERSYSTEM §4.3` is explicit that
  there is *no proved simplicial-identity layer*, and — crucially — building one buys nothing until
  *each face carries its own binding* (the tensor non-finality obstruction of §5). A simplicial
  object with **free** higher fillers would be *unsound* (it would assert exactly the wrong
  factoring `binding_is_proper` forbids). So the only sound simplicial object is a **fibration over
  the bindings**, not a free Kan complex. The ∞-category notation is decorative until the
  per-face-binding fibration is built; the `Hyperedge` + `hyperedge_sound` pair is *the most the
  framing buys today* (`DREGG4-HYPERSYSTEM §4.4`).

### 6.2 What an INFINITY-CELL is — two precise readings `[one REAL, one ASPIRATIONAL]`

The phrase "∞-cell" admits two grounded meanings, and the lens separates them sharply because they
have opposite REAL/ASPIRATIONAL status:

1. **The ∞-cell as the living coalgebra's unbounded life (the codata reading) — `[REAL]`.** A cell
   is a point of `νF` whose unfold is unbounded (`cand-A §1`, `Boundary.TurnCoalg`). The "∞" is the
   **greatest-fixpoint / coinductive** dimension: the cell never bottoms out, and soundness is a
   ▶-guarded bisimulation along the *infinite* trajectory. This is PROVED in
   `Proof/CoinductiveAdversary.lean`: `ObsBisim` is a native Lean-4.30 coinductive predicate
   (`CoinductiveAdversary.lean:113`); `obsBisim_traj_of_bisim` (`:166`) proves confluence-up-to-
   bisimulation along *any* infinite adversarial schedule; `obsBisim_of_uptoComm` (`:436`) derives
   it from the per-step dichotomy alone via ported Paco `gupaco` up-to closure. **The ∞-cell, read
   as "the cell's infinite behaviour folded into one greatest-fixpoint bisimilarity," is REAL and
   axiom-clean.** This is the colimit-of-the-unfold (an ω-colimit of the trajectory) realized
   *behaviourally* — the observation stream is the ω-colimit, and it is proved schedule-robust.

2. **The ∞-cell as the whole history folded into ONE proof-badge (the private-folding reading) —
   `[ASPIRATIONAL]`.** This is the proof-object dual: an ∞-colimit in the category of *proofs*,
   compressing ω-many per-step badges into a single succinct recursive badge (IVC / folding /
   STARK-in-STARK). As §3.3 establishes, this is **deliberately not built** — the architecture ships
   the O(n) forest and defers the O(1) fold behind `RecursionBackend`, arranged so its absence costs
   only succinctness, never soundness (`ProofForest.lean:1–15`, `cand-A §2.4`, `cand-B §5`).

> **The lens's one-line answer.** dregg2 has the ∞-cell *as behaviour* (the coinductive
> greatest-fixpoint over `νF`, PROVED) and the higher-order turn *as a finite wide-pullback gluing*
> (the `Hyperedge`, PROVED), but **not** the ∞-cell *as a single folded proof-object* (the
> private-folding ∞-colimit, ASPIRATIONAL/deferred). The behavioural ∞ is real; the proof-fold ∞ is
> the open frontier. They are dual: the first is the ω-colimit of *observations* (proved), the second
> the ω-colimit of *proofs* (deferred-by-design).

---

## 7. REAL / DECORATIVE / ASPIRATIONAL table (this lens)

| # | Structural claim | Tag | Ground (file:line) | What it would have to prove to be REAL |
|---|---|---|---|---|
| 1 | predicate⊣witness is a Galois connection (the verify side's universal property) | **REAL** | `Laws.predicate_witness_galois` (`Laws.lean:101`), via `polarity_galois` (`Laws.lean:75`) | — (proved: `l A ≤ B ↔ A ≤ u B`) |
| 2 | `find ⊣ verify` as a literal adjunction between the two maps | **DECORATIVE** | `Laws.search_sound` is a by-design `sorry` (`Laws.lean:53–60`) | a unit/counit (`p ≤ verify(find p)`, `find(verify w) ≤ w`); impossible since `find` is undecidable — asymmetry is in the *types* (`Bool` vs `Option`) instead |
| 3 | soundness-by-verification holds against an adversarial prover | **REAL** | `Predicate.adversarial_find_cannot_forge` (`Predicate.lean:151`); `find_untrusted` (`:138`) | — (proved: gate is sole authority; prover never in conclusion) |
| 4 | badge = (permitted ∧ committed), not a grant of standing | **REAL** | `GLOSSARY:153`; `Positional.boundary_law` (`Positional.lean:152`); `VatBoundary.phi_drops_confinement` (`VatBoundary.lean:202`) | — (permission survives crossing, authority does not — proved) |
| 5 | §8 portal: crypto soundness is a `Prop`-carrier, never a Lean law ("the law never learns a secret") | **REAL** | `CryptoKernel.collisionHard` (`CryptoKernel.lean:61`); `MacKernel.unforgeable` (`CaveatChain.lean:87`); `DVKernel.simulate_verifies` (`DesignatedVerifier.lean:102`) | — (named-loss keystones proved from abstract `Verify` alone) |
| 6 | proof-forest composition: per-node validity × `Linked` ⇒ whole-run `StepInv` | **REAL** | `ProofForest.proofForest_sound` (`ProofForest.lean:177`), `proofForest_factors` (`:217`); negative `¬chainLinked` (`:293`) | — (proved, axiom-clean; sheaf gluing bites) |
| 7 | the proof-forest is a *sheaf gluing* (local sections agreeing on overlaps glue) | **REAL** (as a finite limit/gluing) | as #6; `crossForest_attests` (`CrossCellForest.lean:278`), `crossForest_needs_binding` (`:319`) | — (overlap-agreement = `Linked`/CG-5 is load-bearing; proved) |
| 8 | the proof-forest is a *colimit* (with a universal property) | **DECORATIVE** | `proofForest_sound` proves the gluing *equation*, not a mapping-out universal property | an initial/terminal universal property among proofs agreeing on overlaps — none stated |
| 9 | ∞-colimit: fold the whole history into ONE succinct badge (private folding) | **ASPIRATIONAL** | explicitly deferred (`ProofForest.lean:1–15`, `cand-A §2.4`); `-- OPEN:` (`ProofForest.lean:325`) | a recursive verifier whose O(1) badge certifies the O(n)/ω history (the `RecursionBackend`) |
| 10 | ∞-cell as behaviour: coinductive greatest-fixpoint bisimilarity over `νF` along ∞ schedules | **REAL** | `CoinductiveAdversary.ObsBisim` (`:113`), `obsBisim_traj_of_bisim` (`:166`), `obsBisim_of_uptoComm` (`:436`), `stepComplete_carries_infinite` (`:227`) | — (proved, axiom-clean, native coinduction + ported Paco) |
| 11 | tensor non-finality (`νF₁ ⊗ νF₂` not final ⇒ binding irreducible) | **DECORATIVE / corrected (was FALSE)** | `JointTurn.lean:319–333` — the audit calls the slogan "mis-stated"; product of finals IS final | nothing — the true content is #12 |
| 12 | the cross-cell binding (CG-2 ⊗ CG-5) is an irreducible proper-subobject hypothesis | **REAL** | `JointTurn.binding_is_proper` (`:333`); `Hyperedge.hyperedge_sound` (`:374`) + `_needs_binding` (`:409`) | — (proper equalizer/wide-pullback subobject; proved `¬` that it is derivable) |
| 13 | `Φ` (caps→keys) is a *functor* between positional & epistemic authority categories | **ASPIRATIONAL** | `Spec.VatBoundary.phi_functorial` (`VatBoundary.lean:392`) carries one localized `sorry` | identity + composition preservation *with* the loss, for one `Phi stmtOf` over abstract `Verifiable` |
| 13b | `Φ`-functor laws are *inhabited* (a concrete non-degenerate witness) | **REAL** | `phi_functorial_concrete` (`VatBoundary.lean:441`), `#assert_axioms`-clean | — (proved for a concrete discriminating verifier; locates the loss) |
| 14 | conservation `Σ_k` is a *monoid-hom + invariance* | **REAL** | `Core.conservation_ordinary`/`withholding_no_free_copy` (`Core.lean:166,209`) | — (proved from one balance `sorry`) |
| 14b | conservation `Σ_k` is a *strong monoidal functor* | **DECORATIVE** | `Core.lean:11–13` — "functor laws collapse" (discrete target) | functoriality-on-morphisms with non-trivial target — vacuous here |
| 15 | three orthogonal judgements (conservation / I-confluence / ordering) genuinely distinct | **REAL** | `Confluence.top_iconfluent`/`cardLeOne_not_iconfluent` (`:95,104`); separate carriers across `Core`/`Confluence`/`Finality` | — (proved falsifiable distinction) |
| 16 | finality consensus-agreement laws (quorum/commit) | **ASPIRATIONAL** | `Finality.lean:34` — honest `Prop`-`sorry` obligations (tier `LinearOrder` itself is REAL, `:96`) | the distributed-agreement theorems the `sorry`s name |
| 17 | higher-order turn as an n-ary atomic joint-turn (wide pullback) | **REAL** | `Hyperedge` (`:80`), `hyperedge_sound` (`:374`), `legs_agree` (`:111`) | — (proved; N-ary CG-2 cone + CG-5 Σ=0) |
| 18 | the interaction complex is a *full simplicial / ∞-category* (face & degeneracy maps, simplicial identities) | **ASPIRATIONAL** | `DREGG4-HYPERSYSTEM §4.3` — "no proved simplicial-identity layer"; only sound as a fibration-over-bindings | a fibration whose every n-simplex filler is a `Hyperedge` carrying its CG-2 ⊗ CG-5 |

---

## 8. The single sharpest takeaway for this lens

The verify/find seam's real categorical content is **`verify` carrying a Galois adjunction
(predicate⊣witness), with `find` carrying only a contract — the asymmetry living in the types
(`Bool` vs `Option`), not in an adjoint pair.** The proof-forest's real categorical content is a
**finite sheaf gluing** (local `StepInv` sections agreeing on the `Linked`/CG-5 overlaps glue to a
global `StepInv`), PROVED and axiom-clean, with the *colimit/universal-property* framing decorative
and the **∞-colimit (private folding into one badge) aspirational-by-design**. Between them sits the
genuinely-proved **∞-behaviour** (the coinductive bisimulation over `νF` along infinite schedules) —
so dregg2's "infinity" is **real as behaviour, deferred as proof-object.** And the discipline holds:
the two slogans this lens most expected to be decoration over missing theorems —
`tensor_non_finality` and `sound_of_step_complete` — were *both caught false in the Lean and
corrected*, with the soundness content re-grounded on theorems that are actually true
(`binding_is_proper`, `stepComplete_preserves`, the `CoinductiveAdversary` bisimulation). The
category-theory vocabulary, here, did **not** paper over the missing theorems; the Lean exposed
them.
