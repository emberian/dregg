# SHEAF-GROUND-dregg — what dregg ALREADY has that a sheaf-of-verifiers generalizes

> **What this is.** A READ-ONLY grounding of ember's idea — *a metatheory of distributed
> systems should not assume one global Verifier; each party has its own verifier, organized
> as a (pre)sheaf over the parties* — in dregg2's ACTUAL term-proved Lean. Every structural
> claim cites `file:line` in `/Users/ember/dev/breadstuffs/metatheory/Dregg2/`. The discipline
> is the one `DREGG2-FOUNDATIONS.md` enforces: category/sheaf vocabulary is **never** allowed
> to paper over a missing theorem. I tag every mapping **REAL** (a proved Lean theorem with
> teeth backs it), **PARTIAL** (the piece exists but the sheaf shape is not all there), or
> **POETRY** (suggestive only — names what it would have to prove to become real).
>
> **The honest line (kept front and center).** The proof-forest-as-finite-gluing is **REAL**.
> The verifier-indexed `DischargedFor` is the **REAL** first step toward per-party stalks.
> The cohomology-of-consensus (H⁰ = common knowledge, H¹ = forks/bugs/skew) is **POETRY**
> until it cashes out as a theorem. The smallest thing that *would* be a real first theorem is
> stated in §7: **generalize the proof-forest soundness over a verifier-SHEAF** — heterogeneous
> per-node verifiers whose verdicts agree on the linking overlap glue to a sound global verdict.

---

## §0 — The site, the sections, the restriction, the gluing: the dictionary

A sheaf needs four things. dregg already has term-proved analogues of all four — but assembled
around a **single universal verifier**, not a sheaf of per-party verifiers. The whole content of
ember's idea is: *replace the one verifier by a presheaf of verifiers and re-prove the gluing.*

| Sheaf component | What it is | dregg's existing term-proved analogue | Tag |
|---|---|---|---|
| **Site** (the base category of contexts) | who-shares-context; opens = sub-contexts; covers = how contexts decompose | the proof-forest's happened-before DAG (`ProofForest.nodes` + `Linked`); the N-ary `Hyperedge` (the simplicial joint-turn) | **REAL** (as a poset/DAG; **POETRY** as a Grothendieck site) |
| **Section over an open** (local datum) | a per-node verified step | `ProofNode` + its `StepProofValid : Prop` (one cell-step's PI-projection + "this proof verifies") | **REAL** |
| **Restriction map** ρ (datum restricts to a sub-context) | how a verdict on a big context restricts to a shared overlap | the linking discipline `prev.newCommit = next.oldCommit` (intra-cell `chainLinked`) and `Σδ = 0` (cross-cell overlap) | **REAL** (as the *agreement-on-overlap* relation; **PARTIAL** as a functorial ρ with identities) |
| **Gluing / sheaf condition** (local sections agreeing on overlaps ⟹ one global section) | local verified steps that link ⟹ one verified global history | `proofForest_sound` (`ProofForest.lean:177`) and `crossForest_attests` (`CrossCellForest.lean:278`) | **REAL** (finite gluing); **POETRY** (as a colimit universal property) |
| **The verifier index** (the "of-verifiers" part) | each party checks with its own verifier | `DischargedFor : Verifier → Statement → Proof → Prop` (`DesignatedVerifier.lean:113`) | **REAL** as a per-party verdict; the sheaf-OF-VERIFIERS gluing over it is the **OPEN** first theorem (§7) |
| **H⁰ = global section = consensus** | a verdict all parties agree on | `cordial_agreement` (`CordialMiners.lean:336`): a wave anchors ≤ 1 final leader | **REAL** as agreement; **POETRY** as "H⁰" |
| **H¹ = obstruction to gluing = fork/bug/skew** | local sections that *don't* glue | the **negative** `¬ chainLinked [node0, badNode]` (`ProofForest.lean:293`); `Equivocator` / equivocation in `Authority.Blocklace` | **REAL** as a witnessed non-gluing; **POETRY** as "H¹ / cohomology class" |

The rest of this document fills each row in, with the exact Lean.

---

## §1 — THE PROOF-FOREST AS A FINITE SHEAF-GLUING (the REAL anchor)

`Exec/ProofForest.lean` is the load-bearing structure, and `DREGG2-FOUNDATIONS.md:311–318`
already tags it: *"The proof-forest IS a real gluing. … This is a **finite sheaf gluing** (local
sections agreeing on overlaps glue), and the sheaf condition *bites*."* That tag is earned by a
term-proved theorem, axiom-clean (`#assert_axioms proofForest_sound`, `ProofForest.lean:223`).

### 1.1 The SECTIONS — `ProofNode` + `StepProofValid` (`ProofForest.lean:81–98`)

A `ProofNode` is the public-input projection of ONE cell-step — exactly the linking surface
`circuit/src/effect_vm/pi.rs` exposes:

```
structure ProofNode where           -- ProofForest.lean:81
  oldCommit   : Commit               -- pi.rs:17  (input-state commitment)
  newCommit   : Commit               -- pi.rs:20  (output-state commitment)
  effectsHash : Commit               -- pi.rs:24
  prevReceipt : Commit               -- pi.rs:103 (receipt-chain pointer)
  seq         : Nat                  -- pi.rs:204 (monotone replay counter)
  δ           : ℤ                    -- pi.rs:42  (CG-5 signed half-edge)
  StepProofValid : Prop              -- §8 SEAM: "this node's STARK proof verifies against its PI"
```

`StepProofValid` (`:98`) is the **local section's content**: the proposition "the proof over
this open verifies." It is a *named abstract `Prop`*, never a concrete predicate — the §8
cryptographic-soundness seam, entered as DATA exactly like the `CryptoKernel`/`World` portals.

> **MAP TO SHEAF.** A `ProofNode` is a **section of the verifier presheaf over a single open**
> (one cell-step's context). `StepProofValid` is "the local verifier accepts this section."
> **Tag: REAL** — the structure and its seam are term-proved infrastructure.

### 1.2 The RESTRICTION / OVERLAP — `chainLinked` / `Linked` (`ProofForest.lean:137–148`)

```
def chainLinked : List ProofNode → Prop                 -- ProofForest.lean:137
  | a :: b :: rest =>
      a.newCommit = b.oldCommit          -- state continuity across the overlap
      ∧ b.prevReceipt = a.newCommit      -- receipt-chain pointer agrees on the overlap
      ∧ b.seq = a.seq + 1                -- monotone (no replay/fork)
      ∧ chainLinked (b :: rest)
def Linked (pf : ProofForest) : Prop := chainLinked pf.nodes   -- :148
```

This is the **agreement-on-overlap relation**: two adjacent local sections agree exactly when the
prior's `newCommit` equals the next's `oldCommit` (the shared sub-context is the boundary
commitment they share). The receipt pointer and `seq` pin *which* overlap. This is purely
combinatorial — no crypto — and it is *the verifier's PROVED-side check*.

> **MAP TO SHEAF.** `a.newCommit = b.oldCommit` IS the restriction-agreement: section `a`
> restricted to the `a∩b` overlap (its terminal commitment) equals section `b` restricted to the
> same overlap (its initial commitment). **Tag: REAL** as the agreement relation; **PARTIAL** as a
> functorial restriction map — dregg has the *equation* `ρ_a(a) = ρ_b(b)`, not yet ρ as a functor
> with `ρ_id = id` and `ρ∘ρ` coherence (no `Presheaf`/`CategoryTheory` instance exists; grep-empty
> for `sheaf`/`presheaf` in the whole `Dregg2/` tree).

### 1.3 The GLUING — `proofForest_sound` (`ProofForest.lean:177`, PROVED, axiom-clean)

```
theorem proofForest_sound (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid)   -- (P) every local section verifies  [ASSUMED §8 seam]
    (_hlinked : Linked pf) :                        -- (L) sections agree on overlaps    [PROVED-side check]
    fullProofForestInv pf := by                     -- ⟹ ONE global verified history
  unfold fullProofForestInv
  exact execForest_attests (pf.attested hvalid)
```

`fullProofForestInv` (`:161`) unfolds to `fullForestInv pf.s pf.witness pf.s'` = the four-conjunct
`StepInv` over the whole forest (Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance). The proof
discharges the §8 portal `pf.attested` (`:124`: `(∀ n, StepProofValid) → execForest s witness =
some s'`) to a real committed run, then `execForest_attests` (`TurnForest.lean:290`) attests all
four conjuncts.

> **MAP TO SHEAF — this is the gluing axiom, term-proved.** *Local sections that all verify (P)
> AND agree on their overlaps (L) ⟹ a global section (the whole-forest `StepInv`).* The split is
> exactly the sheaf split: **(P) is the per-open local data; (L) is the compatibility-on-overlaps
> condition; the conclusion is the unique global section.** **Tag: REAL.**

### 1.4 The sheaf condition BITES — the non-gluing witness (`ProofForest.lean:293`, PROVED)

The gluing is non-vacuous *because* there is a witnessed failure to glue:

```
def badNode : ProofNode := { oldCommit := 99, … StepProofValid := True }   -- :288
example : ¬ chainLinked [node0, badNode] := by …                          -- :293  (1 = 99 fails)
```

Each node individually verifies (`StepProofValid := True`), yet they DO NOT glue: `node0.newCommit
(1) ≠ badNode.oldCommit (99)`. The verifier rejects at the overlap check.

> **MAP TO SHEAF — this is the H¹-flavored obstruction, made concrete.** Two locally-valid
> sections that disagree on the overlap are NOT a global section. In ember's framing this is
> *precisely* a fork / bug / version-skew: each party's local verdict is fine, but they fail to
> glue. **Tag: REAL as a witnessed non-gluing; POETRY as a cohomology class** (there is no
> `H¹` object, no Čech complex, no coboundary map — see §6).

### 1.5 The CROSS-CELL overlap — `Σδ = 0` (`CrossCellForest.lean:278`, PROVED)

When edges cross cells, the overlap is no longer `new = old` continuity but the CG-5 N-ary
shared-binding `Σδ = 0`:

```
theorem crossForest_attests (f : CrossCellForest) … (sid : SharedId) …
    (hbind : ∑ i, (crossForestTurn f sid).δ i = 0)            -- the cross-cell OVERLAP condition
    (h : execCrossForest f cellOf sid = some cells') :
    fullCrossForestInv f cellOf sid cells' := …                -- CrossCellForest.lean:278
```

The `δ` half-edge is already a field on `ProofNode` (`ProofForest.lean:93`), and `ProofForest`'s
own module-foot (`:325–330`) names the cross-cell forest as the natural next gluing — its `Linked`
would be `Σδ = 0` over a family rather than `new = old`.

> **MAP TO SHEAF.** This is a **second restriction/overlap law on the same site**: cross-cell
> opens glue when their signed half-edges sum to zero (a balance overlap, valued in a commutative
> monoid). **Tag: REAL** as the cross-cell gluing; it makes the "overlap" notion genuinely
> richer than continuity alone — the site has two kinds of cover (intra-cell sequential, cross-cell
> hyperedge).

**Is it literally a SHEAF, a PRESHEAF, or just a gluing?** Honestly: **it is a finite gluing /
equalizer-flavored sheaf condition, not a constructed (pre)sheaf object.** There is no
`CategoryTheory.Sheaf`, no presheaf functor, no Grothendieck topology in the Lean (grep-confirmed:
the word "sheaf" never appears in `Dregg2/`; `DREGG2-FOUNDATIONS.md:318` says the colimit/universal
-property reading is **DECORATIVE**). What is REAL is the *gluing equation* (P)∧(L)⟹global, with the
sheaf condition biting (§1.4). To become a genuine sheaf one would build the presheaf
`Open ↦ {verified sections}` with functorial ρ and show the gluing map is an iso onto compatible
families — that is buildable on top of §1.1–1.5, and it is half of the §7 first theorem.

---

## §2 — THE VERIFIER-INDEXED `DischargedFor` (the per-party stalk — REAL first step)

`Authority/DesignatedVerifier.lean` closes the *transferability* gap, and in doing so it builds
**exactly the missing verifier index** ember's idea needs. The module's own opening
(`:6–19`) states the gap: the running system's `presentation.rs:224 verify(&self)` and the Lean
`Laws.Discharged` (`Laws.lean:38`) are a **single UNIVERSAL verify relation, NOT indexed by who is
checking** — "the model therefore cannot even EXPRESS 'convincing only to verifier V'."

### 2.1 The stalk-at-a-party — `DischargedFor` (`DesignatedVerifier.lean:113`)

```
def DischargedFor [DVKernel Verifier Statement Proof VSecret]      -- DesignatedVerifier.lean:113
    (V : Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  DVKernel.verifyFor (VSecret := VSecret) V stmt proof = true     -- verifyFor : Verifier → … → Bool  (:89)
```

`verifyFor` (`:89`) is the **verifier-INDEXED verify oracle** — "unlike `CryptoKernel.verify` and
`presentation.rs::verify`, the verdict may depend on *who* is checking" (`:86–88`). This is the
literal "each party has its own verifier."

> **MAP TO SHEAF.** `DischargedFor V s p` is **the section's germ at the stalk over party `V`** —
> "verifier `V`'s local verdict on this statement/proof." The presheaf assigns to each party `V`
> its set of verdicts; `DischargedFor V` is membership in that stalk. **Tag: REAL** — this is the
> one place in dregg the verdict is genuinely indexed by the checking party.

### 2.2 The PUBLIC endpoint = the `∀V` collapse = the global section that already exists

```
def Transferable (Verifier : Type) … (stmt) (proof) : Prop :=     -- DesignatedVerifier.lean:129
  ∀ V : Verifier, DischargedFor (VSecret := VSecret) V stmt proof  -- convinces EVERY party
theorem public_convinces_any_third_party … (W : Verifier) :       -- :176  (PROVED)
    DischargedFor (VSecret := VSecret) W stmt proof := h W
theorem publicMode_collapses_to_universal … :                     -- :186  (PROVED, Iff.rfl)
    DialHolds .transferable stmt proof ↔ ∀ V, DischargedFor V stmt proof
```

> **MAP TO SHEAF — this is the load-bearing bridge.** The CURRENT dregg behaviour (one universal
> verifier) is **exactly `∀V, DischargedFor V`** — i.e. a section in the stalk over *every* party
> at once, a **constant global section of the verifier presheaf.** `public_convinces_any_third_party`
> is, in sheaf language, "a global (constant) section restricts to a section over each party `W`."
> `DREGG2-FOUNDATIONS.md:235` independently flags this as "the single closest thing to a presheaf
> restriction map in the whole codebase." **Tag: REAL as the restriction-of-the-constant-section;
> POETRY as a full restriction functor** (it is one map per `W`, not yet a functor with identities/
> composition).

### 2.3 The DESIGNATED endpoint = a section that does NOT glue to a global one (the teeth)

```
theorem designated_not_transferable … (h : DesignatedFor V₀ stmt proof) :  -- :206  (PROVED)
    ∃ W : Verifier, ¬ DischargedFor (VSecret := VSecret) W stmt proof
theorem designated_is_deniable (V₀) (stmt) :                               -- :224  (PROVED)
    ∃ proof, DischargedFor V₀ stmt proof ∧ proof = simulate (vsecret V₀) stmt
```

A designated-verifier transcript sits in the stalk over `V₀` but `designated_not_transferable`
extracts a *concrete* party `W` whose stalk it is NOT in.

> **MAP TO SHEAF — heterogeneity made real.** This is a section that is genuinely **local to one
> party and does not extend to a global section** — the verifier-presheaf has a section over `{V₀}`
> with no gluing to the cover. In ember's framing this is the cleanest possible witness that "the
> single-global-verifier assumption is wrong": there provably exist sections (verdicts) that one
> party accepts and another provably rejects, with a *witnessed* separation (`dial_endpoints_distinct`,
> `:346`, over a concrete 2-verifier reference kernel). **Tag: REAL.** This is the strongest existing
> evidence that the sheaf-of-verifiers is the right shape: dregg already has heterogeneous,
> non-gluing local verdicts as a *proved* phenomenon.

---

## §3 — THE verify/find GALOIS SEAM (`Laws.lean`, the verifier-as-the-adjoint-side)

`DREGG2-FOUNDATIONS.md:294–304` tags this REAL with a sharp correction: *it is `verify`, not `find`,
that carries the universal property.*

```
def Discharged [Verifiable P W] (p : P) (w : W) : Prop := Verify p w = true   -- Laws.lean:38
theorem predicate_witness_galois [Verifiable P W] :                            -- Laws.lean:101  (PROVED)
    GaloisConnection
      (fun A : Set P => toDual {w | ∀ p ∈ A, Discharged p w})
      (fun B : (Set W)ᵒᵈ => {p | ∀ w ∈ ofDual B, Discharged p w})
```

The Galois connection is the Birkhoff polarity of the `Discharged` relation (`polarity_galois:75`,
fully proved). `find` (`Searchable.find`, `:48`) is the opaque, untrusted, possibly-nonterminating
search side; `search_sound` (`:53`) is a by-design `sorry` (`:60`) — *a contract on an external
plugin*, never an in-Lean theorem.

> **MAP TO SHEAF.** The seam tells us *which side is the verifier* — and it is the side with the
> universal property (the right adjoint / closure). In a sheaf-of-verifiers, this is the structure
> on each stalk: each party's verdict relation `Discharged` (here universal; `DischargedFor` in §2
> when indexed) induces its own polarity adjunction. **Tag: REAL** for the seam itself; mapping the
> Galois adjunction *into* a per-stalk structure is **POETRY** today (no per-`V` `predicate_witness_galois`
> is stated). The honest content: the seam pins **the verifier as the TCB**, which is precisely the
> object the sheaf is a sheaf *of*.

---

## §4 — CORDIAL-MINERS CONSENSUS = the H⁰ / global-section content (`CordialMiners.lean`)

`Proof/CordialMiners.lean` models the *actual* DAG-BFT dregg1 runs (`blocklace/src/ordering.rs`),
not classical voting BFT, and proves agreement (`cordial_agreement:336`, `cordial_agreement_from_lace
:484`, both `#assert_axioms`-clean).

```
def Committed (S) (cfg) (l : Block) : Prop :=                  -- CordialMiners.lean:279
  Nonempty (superRatifiedFromLace S cfg l)                     -- the lace EXHIBITS a ≥ n−f ratifier quorum
theorem cordial_agreement (S) (cfg) (l₁ l₂)
    (sr₁ : SuperRatification S cfg l₁) (sr₂ : SuperRatification S cfg l₂)
    (M : BFTModel cfg (sr₁.votes ++ sr₂.votes)) … :
    l₁ = l₂                                                    -- :336  a wave anchors ≤ 1 final leader
```

Agreement is proved by *quorum intersection at an honest party*
(`BFT.honest_witness_in_intersection`, transferred onto the DAG): two `n−f` ratification quorums
share an honest ratifier, whose honesty law forces the two leaders equal. The ratifying-voter set
is **read off the real blocklace** (`ratifyingVoters`, `:157`; `superRatifiedFromLace.quorum_from_lace`,
`:241`), not assumed.

> **MAP TO SHEAF — consensus IS the global section.** A committed block is a verdict that **a
> super-majority of parties' local verifiers agree on** (each ratifier's `approves` read is its own
> local verdict; `CordialState.approves:143`). `cordial_agreement` says these per-party local
> verdicts **glue to at most one global section per wave** — exactly "H⁰ = the globally-agreed
> verdict = common knowledge." The honest-party-in-the-intersection IS the overlap on which the
> local sections must agree. **Tag: REAL as agreement (a proved unique-global-section-per-wave);
> POETRY as "H⁰"** (there is no cohomology object; the agreement is a quorum-intersection theorem,
> and the network-convergence half is the honest `World.recv_mono` portal (`World.lean:98`) +
> the named `OPEN-CM-DISSEMINATION`, not derived).

> **The dual — equivocation = a non-gluing class.** `Authority.Blocklace.Equivocator`
> (used at `CordialMiners.lean:144`, `honest_no_equivocation` at `:588`) is the witnessed
> failure of a party's sections to be comparable — a Byzantine party emitting two incomparable
> blocks is precisely a local datum that **cannot** glue. This is the consensus-layer analogue of
> §1.4's `¬ chainLinked`. **Tag: REAL as the non-gluing witness; POETRY as "an H¹ class."**

---

## §5 — THE HYPEREDGE / JOINT-TURN SIMPLICIAL SITE (`Hyperedge.lean`)

`Hyperedge.lean` builds the N-ary atomic joint-turn as a **wide pullback over `TurnId`** — the
honest simplicial site of who-shares-a-turn.

```
structure Hyperedge (ι) [Fintype ι] (T) (turnId) (halfEdge) where    -- Hyperedge.lean:80
  x   : ι → T.Carrier                          -- the participant tuple (the simplex's vertices)
  tid : TurnId                                 -- the APEX (Mina's account_updates_hash)
  agree : ∀ i, turnId i (T.next (x i) t) = tid -- CG-2 cone: every leg factors through one apex
  balanced : (Finset.univ.sum fun i => halfEdge i (x i) t) = 0    -- CG-5: one Σ=0 over the simplex
theorem Hyperedge.legs_agree (H) (i j) :                            -- :111  (PROVED)
    turnId i (T.next (H.x i) H.t) = turnId j (T.next (H.x j) H.t)   -- pairwise agreement for FREE
```

`legs_agree` (`:111`, PROVED) is the cone collapsing: the `O(N²)` pairwise agreements of a
family-of-binary-edges are recovered from the single apex. `hyperedge_sound` (`:374`, PROVED,
axiom-clean) is the N-ary soundness; `hyper_binding_is_proper` (`:164`) / `hyper_not_all_admissible`
(`:505`) prove the joint behaviour is a **proper subobject** (per-cell data cannot supply it).

> **MAP TO SHEAF — this is the SITE.** The set of incidences `ι` of a hyperedge is **a simplex of
> the who-shares-context complex**; the apex `tid` is the shared sub-context all participants
> restrict to; `agree` (CG-2) is the cone/compatibility condition; `balanced` (CG-5) is the overlap
> conservation law. A turn incident to parties `{Cᵢ}` is exactly an open of the site that those
> parties cover. **Tag: REAL as the simplicial site / wide-pullback** (the construction and its
> soundness are proved); **POETRY as a Grothendieck topology / Kan complex** — and crucially
> `DREGG2-FOUNDATIONS.md:208–215` proves it **must NOT be a free Kan complex** (a face of a balanced
> hyperedge is generally unbalanced — `hyper_not_all_admissible`), so the only sound sheaf is a
> **fibration over the bindings**, never a free complex. This is a *constraint the sheaf-of-verifiers
> must respect*: the covers are the bindings, and gluing across a partition can be unfillable
> (`DREGG2-FOUNDATIONS.md:388`, the partition non-fillability `REAL-as-impossibility`).

---

## §6 — THE COHOMOLOGY: separate the REAL gluing from the H⁰/H¹ poetry

ember's H⁰/H¹ reading is **suggestive and well-aimed**, but it is **POETRY until it cashes out as a
theorem.** Stated precisely, with the discipline of `DREGG2-FOUNDATIONS.md`:

- **H⁰ = globally-agreed verdicts = consensus / common knowledge.** dregg HAS the *content* (the
  unique global section): `proofForest_sound` (one verified history), `cordial_agreement` (one final
  leader per wave), `Transferable`/`public_convinces_any_third_party` (one verdict for all parties).
  What it does NOT have: an `H⁰` *object* — no global-sections functor `Γ`, no `H⁰ = ker(δ⁰)`.
  **The content is REAL; the name "H⁰" is POETRY.**

- **H¹ = the OBSTRUCTIONS = forks, bugs, version-skew, Byzantine disagreement.** dregg HAS witnessed
  *non-gluing*: `¬ chainLinked [node0, badNode]` (`ProofForest.lean:293`), `designated_not_transferable`
  (`DesignatedVerifier.lean:206` — a party that provably rejects), `Equivocator` (Byzantine
  disagreement). What it does NOT have: an `H¹` *object* — no Čech complex over the cover, no
  coboundary map δ⁰: sections → overlaps, no "obstruction class is nonzero iff no global section."
  **The witnesses are REAL; the name "H¹ class" is POETRY.**

> **The exact gap to close before "cohomology" earns its keep.** Build the Čech-style 2-term complex
> over the proof-forest cover: `C⁰ = ∏_opens (verified sections)`, `C¹ = ∏_overlaps (agreement
> residuals)`, `δ⁰ s = (ρ_a s_a − ρ_b s_b)_overlaps`. Then **`ker δ⁰` = `Linked` families = §1.3's
> hypothesis**, and the theorem "`δ⁰ s = 0 ⟹ ∃! global section`" is *exactly* `proofForest_sound`
> re-read. `H¹ = coker δ⁰ ≠ 0` would then literally classify "locally-valid-but-unglueable" = the
> fork/bug/skew. This is buildable — but it is NOT built, and **calling the current gluing
> "cohomology" today would let sheaf vocabulary paper over the missing complex.** The discipline:
> ship the gluing as a gluing (REAL), label the cohomology as the next theorem (OPEN).

---

## §7 — THE SMALLEST REAL FIRST THEOREM: proof-forest soundness over a verifier-SHEAF

Everything above is assembled around a **single** verifier (the proof-forest's `StepProofValid` is
one abstract `Prop` per node, the *same* notion of "valid" at every node; the `World`/consensus
verdicts are universal). The genuine generalization ember's idea asks for — and the smallest one
that would be **REAL and buildable** — is to **index the proof-forest's validity by a per-node
verifier** and re-prove the gluing.

### 7.1 The generalization, stated

Currently (`ProofForest.lean:81–124`): one `StepProofValid : Prop` per node, and a single portal
`attested : (∀ n, n.StepProofValid) → execForest s witness = some s'`.

**The verifier-sheaf generalization (NEW, the first theorem):**

1. Give each `ProofNode` its **own verifier** `Vᵢ` and its own verdict via §2's `DischargedFor`:
   replace the uniform `StepProofValid` with `DischargedFor Vᵢ (stmtOf nᵢ) (proofOf nᵢ)` — *node `i`
   is checked by party `i`'s verifier* (heterogeneous software / upgrades / bugs all live here:
   different `Vᵢ` = different section, exactly ember's "different software per node").
2. Keep the **overlap-agreement** `Linked` (`:148`) UNCHANGED — it is verifier-independent
   (it is about commitments, not about who checks): the restriction maps still agree on overlaps.
3. **The theorem to prove (`proofForest_sheaf_sound`):**
   > *If every node's section is accepted by ITS OWN verifier (`∀ i, DischargedFor Vᵢ …`) AND the
   > sections agree on overlaps (`Linked`), THEN there is a sound global verified history
   > (`fullProofForestInv`) — PROVIDED the per-node verifiers are sound on the shared overlap
   > surface (a per-overlap compatibility hypothesis: `Vᵢ` and `Vⱼ`'s verdicts on the shared
   > commitment agree).*

This is **`proofForest_sound` GENERALIZED over a verifier-sheaf**: the conclusion is unchanged; the
hypothesis (P) is replaced by *heterogeneous per-party local verdicts*; the new content is the
**overlap-compatibility of the per-node verifiers** — which is the literal sheaf condition for a
*sheaf of verifiers* rather than a sheaf with one verifier.

### 7.2 Why it is REAL and buildable (not poetry)

- The pieces all exist and are term-proved: `DischargedFor` (`:113`) supplies the per-party verdict;
  `Linked` (`:148`) supplies the overlap relation; `proofForest_sound` (`:177`) supplies the gluing
  spine; `public_convinces_any_third_party` (`:176`) supplies the collapse "uniform verifier =
  constant section" so the new theorem **specializes back** to the existing one when all `Vᵢ` are
  equal (the non-vacuity / backward-compat check).
- The new hypothesis (overlap-compatibility of `Vᵢ`, `Vⱼ`) is precisely what ember's framing wants
  to make load-bearing: **a software bug / version-skew is a verifier `Vᵢ` whose verdict disagrees
  with `Vⱼ` on the overlap → the compatibility hypothesis FAILS → no global section.** That is the
  H¹-obstruction, now as a *real failed hypothesis of a real theorem*, witnessed exactly as
  `designated_not_transferable` (`:206`) already witnesses a disagreeing verifier.
- It respects the proven constraints: §5's fibration-over-bindings (covers are bindings, not free
  fillers) and §1.5's two overlap laws (`new = old` intra-cell, `Σδ = 0` cross-cell).

### 7.3 What stays OPEN after that first theorem

- The **cohomology object** (§6): even `proofForest_sheaf_sound` is a gluing *equation*, not a
  Čech `H¹`. Building `δ⁰`/`H¹` is the *second* step, and only then does "cohomology of consensus"
  earn the word.
- The **functorial restriction maps with identities/composition** (§1.2, §2.2): the first theorem
  uses the agreement *relation*, not a presheaf functor; promoting `Linked` and
  `public_convinces_any_third_party` to a genuine `Presheaf` with ρ-coherence is additional work.
- The **upgrade/version axis** (ember's v1-vs-v2 = different sections): expressible the moment `Vᵢ`
  varies, but a *theorem* about backward-compat (= "v2's verdict restricts to v1's on the shared
  sub-protocol") is its own statement, modeled on `Upgrade.lean`'s `no_downgrade`/genealogy spine.

---

## §8 — VERDICT (the honest ledger)

| Claim | Tag | Receipt |
|---|---|---|
| Proof-forest is a finite SHEAF-GLUING (local valid + agree-on-overlap ⟹ global) | **REAL** | `proofForest_sound` `ProofForest.lean:177`, axiom-clean `:223` |
| The sheaf condition BITES (valid-but-unglueable is witnessed) | **REAL** | `¬ chainLinked [node0, badNode]` `ProofForest.lean:293` |
| Cross-cell overlap = `Σδ = 0` (a second cover/restriction law) | **REAL** | `crossForest_attests` `CrossCellForest.lean:278` |
| Verifier-INDEXED verdict = the per-party stalk | **REAL** | `DischargedFor` `DesignatedVerifier.lean:113` |
| Heterogeneous, non-gluing local verdicts EXIST (the sheaf-of-verifiers is the right shape) | **REAL** | `designated_not_transferable` `:206`, `dial_endpoints_distinct` `:346` |
| Uniform verifier = constant global section (the `∀V` collapse / restriction-of-constant) | **REAL** | `public_convinces_any_third_party` `:176`, `publicMode_collapses_to_universal` `:186` |
| Consensus = a unique global section per wave (the H⁰ content) | **REAL** | `cordial_agreement` `CordialMiners.lean:336` |
| Hyperedge = the simplicial who-shares-context SITE | **REAL** | `Hyperedge` `:80`, `legs_agree` `:111`, `hyperedge_sound` `:374` |
| Verify (not find) is the adjoint side = the verifier-as-TCB the sheaf is OF | **REAL** | `predicate_witness_galois` `Laws.lean:101` |
| It is a constructed (pre)SHEAF object with functorial ρ / Grothendieck topology | **POETRY / PARTIAL** | no `Sheaf`/`Presheaf` in `Dregg2/` (grep-empty); `DREGG2-FOUNDATIONS.md:318` colimit = DECORATIVE |
| H⁰ / H¹ as cohomology OBJECTS (Čech complex, δ⁰, classes) | **POETRY** | no complex, no coboundary, no `H` object anywhere; §6 names the gap |
| **`proofForest_sheaf_sound`: proof-forest soundness over a verifier-SHEAF** | **OPEN → REAL+buildable** | the smallest real first theorem, §7 — all inputs term-proved |

**One-line synthesis.** dregg already proves the proof-forest is a finite gluing and already has a
verifier-indexed verdict (`DischargedFor`) plus *proved heterogeneous non-gluing verdicts*; the
SMALLEST real generalization — `proofForest_sound` re-proved with a DIFFERENT verifier per node and
an explicit overlap-compatibility hypothesis — is buildable today from those term-proved pieces, and
it is *that* theorem, not the cohomology vocabulary, that makes "sheaf of verifiers" earn its keep.
The cohomology (Čech `H⁰`/`H¹`) is the honest second step, deliberately labeled POETRY until the
coboundary complex is built — so the sheaf vocabulary never papers over the missing theorem.

( ⌐■_■ ) the egg dreams of many eyes, and proves a few of them already disagree.
