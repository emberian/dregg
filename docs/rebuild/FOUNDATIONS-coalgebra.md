# FOUNDATIONS-coalgebra — the cell as a (final) coalgebra, excavated against the Lean

> **What this is.** A READ-ONLY excavation of dregg2's categorical foundations through ONE
> lens: **the cell as a point of a final coalgebra**. The fulcrum is honesty — every
> structural claim is tagged **REAL** (the universal property / law is actually *proved* in
> the Lean), **DECORATIVE** (suggestive notation that buys no theorem; I say what it would
> have to prove to become real), or **ASPIRATIONAL** (claimed by the design but actually a
> `sorry` / `-- OPEN` / refuted-and-downgraded). No code changed.
>
> **The discipline (carried from `REORIENT §6` / `study-category §0`):** category-theory
> vocabulary must not paper over a missing theorem. "Final coalgebra", "functor",
> "bisimulation", "∞-category" each earn their keep only by a *binding* fact in the Lean.
> Where they don't, I flag it.
>
> **Sources read in full.** Docs: `study-category.md`, `cand-A-vat-coalgebra.md`,
> `cand-B-witness-pca.md`/`cand-C-cap-distributed.md` (skim), `GLOSSARY.md`, `REORIENT.md`,
> `pdfs/STUDY-lean4-coinduction.md`, `DREGG4-HYPERSYSTEM.md`, `CARRY-FORWARD-SYNTHESIS.md`,
> `Finality.lean`-anchored `decisions`-equivalents. Lean (the artifact, `file:line` are
> receipts): `Dregg2/Boundary.lean`, `Core.lean`, `JointTurn.lean`, `Hyperedge.lean`,
> `Confluence.lean`, `Finality.lean`, `Resource.lean`, `Spec/VatBoundary.lean`,
> `Spec/JointViaHyper.lean`, `Proof/CoinductiveAdversary.lean`, `Exec/Cell.lean`,
> `Exec/CrossCellForest.lean`, `Paco/Basic.lean`, `Paco/Companion.lean`.

---

## 0. TL;DR — what is *actually* established categorically

The headline, sharpened against the Lean and against the prior `study-category.md` verdict
(which predates several modules):

1. **The behaviour functor `F X = Obs × (AdmissibleTurn ⇒ X)` is REAL** — it is a literal
   Lean definition (`Boundary.F`, `Boundary.lean:66`), and the coalgebra structure-map
   `TurnCoalg.step : Carrier → F Carrier` is a real structure (`Boundary.lean:74`). A cell
   *is* a point of a coalgebra of this functor, instantiated concretely in
   `Exec/Cell.lean:42` (`livingCell`).

2. **"Final coalgebra `νF`" is NOT proved as a finality/terminal universal property — it is
   ASPIRATIONAL-as-finality but REAL-as-relational-gfp.** `Boundary.lean` works over an
   *arbitrary* `TurnCoalg` and never constructs `νF`, never proves a terminal universal
   property (no unique anamorphism into behaviours, no `Cofix`/QPF). `grep` confirms **zero**
   `MvQPF`/`Cofix` codata-value construction anywhere in `Dregg2/` (the two mentions are
   comments saying "no QPF, no codata datatype" — `Exec/Cell.lean:14`). What *is* real is the
   **bisimulation principle** (the relational greatest fixpoint): `IsBisim`, `Sound`, and — in
   `Proof/CoinductiveAdversary.lean` — a genuine **native `coinductive ObsBisim`** with its
   auto-generated coinduction principle `ObsBisim.coinduct`. Finality (uniqueness of the
   anamorphism) is the universal property that is *gestured at* but never discharged.

3. **The headline soundness keystone changed shape, and that change is the most important
   honesty fact in this lens.** The original `sound_of_step_complete` (step-completeness ⇔
   bisimilar-to-a-free-`Spec`) was found **false-as-stated** (refuted at `Spec.Carrier =
   Empty`) and **removed** from `Boundary.lean`. What survives there is (a) `stepComplete_preserves`
   — a *safety-invariant* theorem (REAL, PROVED), and (b) `Sound`/`IsBisim` as a *behavioural-
   equivalence* notion with reflexivity (`sound_refl`). The genuine bisimulation keystone was
   then **recovered honestly for a CONCRETE cell** in `Exec/Cell.lean`: `livingCell_sound`
   proves the running cell is bisimilar to a real conservation oracle, via the golden-oracle
   bridge `bisim_of_oracle` (REAL, PROVED, 0 sorries in that file).

4. **Step-completeness IS the contractivity / well-definedness condition** — and this is
   half-REAL: it is the load-bearing hypothesis of every real soundness theorem
   (`stepComplete_preserves`, `livingCell_sound`, the infinite-schedule lift), exactly as the
   "drifting future = non-contractive infinite coherence" framing predicts. But Lean's kernel
   does *not* enforce productivity here (`Later := id`, `Boundary.lean:103`); productivity is
   *assumed*, the real bite moved into `StepComplete`. So "contractivity" is REAL as a
   load-bearing premise, DECORATIVE as a kernel-checked guard.

5. **The vat-boundary `Φ` being a functor (caps→keys) is ASPIRATIONAL** — `phi_functorial` is
   the single genuine proof-body `sorry` in this lens (`Spec/VatBoundary.lean:401`). Its named
   loss, monotonicity, and domain are REAL (proved); its *functoriality* is open, with a
   concrete witnessed instance (`phi_functorial_concrete`) proving the laws are inhabited.

The rest of this doc grounds each of these `file:line` and tags them.

---

## 1. The functor and the coalgebra structure-map — REAL

`Boundary.lean:66`:
```
abbrev F (Obs AdmissibleTurn : Type u) (X : Type u) : Type u := Obs × (AdmissibleTurn → X)
```
and `Boundary.lean:74`:
```
structure TurnCoalg (Obs AdmissibleTurn : Type u) where
  Carrier : Type u
  step    : Carrier → F Obs AdmissibleTurn Carrier
```
with projections `TurnCoalg.obs` (`:81`) and `TurnCoalg.next` (`:87`). This is a textbook
**Moore/DFA coalgebra**: output-on-state (`obs`), transition-on-input (`next`), the input
alphabet being the *dependent* `AdmissibleTurn`. The codomain of `next` is again `Carrier` —
codata: a cell transitions to another live cell, never to a "final state" (`:86` doc).

**This is genuinely load-bearing, not cosplay.** The `cand-A §1.2` slogan "the morphism *is*
the object's behaviour; one primitive, two faces" is literally true here: there is no separate
`Turn` object inside `Boundary`; a turn is the action of `step`, the edge `next x t`. The
two-co-primitives tension the spine docs worried about is dissolved by the functor.

> **Tag: REAL.** `F` and `TurnCoalg` are honest definitions; a cell is a point of such a
> coalgebra (`Exec/Cell.lean:42` instantiates one concretely). The functor framing earns its
> keep — it is the type that *carries* `obs`/`next` and over which every soundness statement
> quantifies.

**One subtlety the design names and the Lean honors:** `F` is a polynomial/QPF functor (a
constant `Obs` times an exponential by a fixed `AdmissibleTurn`), so its final coalgebra
*exists* in principle (`STUDY-lean4-coinduction §2.3`). But "exists in principle" ≠ "constructed
and proved final in this Lean" (see §2).

---

## 2. Is the cell *actually* the FINAL coalgebra in the Lean? — ASPIRATIONAL-as-finality, REAL-as-gfp

This is the crux of the lens. The design (`cand-A §1.1`, `GLOSSARY: cell`) asserts:

> a cell is an element of the **final coalgebra `νF`** … `Cell = νC. µI. StepProof I × (Turn ⇒ C)`.

**What "final" would require (the universal property):** for every coalgebra `(X, c)`, a
*unique* coalgebra homomorphism `X → νF` (the anamorphism `⟦c⟧`), making `νF` terminal in the
category of `F`-coalgebras. Bisimilarity then collapses to equality on `νF` (`Cofix.bisim`).

**What the Lean actually has:**

- **No `νF` is constructed.** `STUDY-lean4-coinduction §0/§2.1` is explicit and the codebase
  matches: the scaffold "never builds the codata type `νC`"; it "works with an arbitrary
  `TurnCoalg` … and states soundness as the existence of a relational bisimulation." `grep`
  confirms no `MvQPF`/`Cofix`/`Cofix.corec`/`Cofix.bisim` anywhere in `Dregg2/`. The keystone
  nested-fixpoint type `Cell = νC. µI. …` appears **only in prose** (`Boundary.lean:14` header,
  `cand-A §2.1`, `GLOSSARY`) — there is no Lean term of that type.

- **No terminal universal property is proved.** There is no theorem "for every coalgebra there
  is a unique morphism into a distinguished one." The anamorphism is not defined as a Lean
  function; checkpoint/restore/replay are proved over a *concrete* carrier (`ChainedState`,
  `Exec/Cell.lean`), not as anamorphism-re-seeding on `νF`.

- **What IS real is the relational greatest fixpoint + a native coinductive predicate:**
  - `IsBisim` (`Boundary.lean:117`): the closure property a witness relation must satisfy
    (`obs_eq` now, `step_rel` later). This is the *post-fixpoint* presentation of bisimilarity.
  - `Sound` (`Boundary.lean:130`): `∃ R y, IsBisim R ∧ R x y` — the Knaster–Tarski
    "exists a bisimulation" form.
  - `bisim_eq` (`Boundary.lean:203`, PROVED) and `sound_refl` (`Boundary.lean:211`, PROVED):
    equality is a bisimulation; every cell is sound relative to itself.
  - **`coinductive ObsBisim`** (`Proof/CoinductiveAdversary.lean:113`): a *genuine* Lean-4.30
    native coinductive predicate (the **largest** such relation, not just the closure
    property), with the auto-generated `ObsBisim.coinduct` principle used at `:175`, `:376`.

> **Tag: ASPIRATIONAL** for "the cell is the FINAL coalgebra `νF`" *as a finality/terminal
> universal property* — it is nowhere proved, and no `νF` value exists. To become REAL it would
> have to: (i) register `F` as an `MvQPF`, (ii) define `Cell := MvQPF.Cofix F`, (iii) prove the
> terminal universal property (unique anamorphism) or at least `Cofix.bisim` (bisimilarity ⇒
> equality on `Cell`). `STUDY-lean4-coinduction §4.1` argues this is *avoidable and deferrable*
> precisely because the soundness theorem is relational — so the design's choice to *not* build
> `νF` is principled, but it means "final" is a name, not a theorem.
>
> **Tag: REAL** for the **bisimulation principle / relational gfp** — `IsBisim`/`Sound`/
> `bisim_eq`/`sound_refl` are honest, and `ObsBisim` + `ObsBisim.coinduct` is a true greatest
> fixpoint with a real coinduction principle. The cell is faithfully modelled as *a point of a
> coalgebra whose soundness is bisimilarity*, which is strictly weaker than "the point of the
> final coalgebra" but is what every downstream theorem actually uses.

**Net:** dregg2 has the **coalgebra** and the **bisimulation**, not the **finality**. The
slogan "point of the final coalgebra" is the design's *ontology*; the Lean's *theorem* is "a
coalgebra carrier whose states are sound iff bisimilar to a golden oracle." Honest naming would
be "the cell is a point of *a* coalgebra, sound by bisimulation" — finality is the aspiration.

---

## 3. The ▶-guarded bisimulation as soundness — and the FALSE-as-stated keystone, dug up precisely

This is the history the brief asks to dig up. It is a model case of the project's "no
fake-to-pass" discipline catching itself.

### 3.1 What `sound_of_step_complete` originally claimed, and why it was FALSE

The original `Boundary.lean` stated (per its own §"meaningful soundness keystone" note,
`Boundary.lean:156–200`, and `REORIENT §4`):

> `sound_of_step_complete : (∀ step, StepComplete) → Sound Impl Spec x`
> `step_complete_of_sound : Sound Impl Spec x → StepComplete`

with `Spec` a **free parameter** coalgebra. This is **machine-checkably false**: instantiate
`Spec.Carrier = Empty`. Then `Sound Impl Spec x = ∃ (R) (y : Empty), …` is **uninhabited** (no
`y : Empty`), while `StepComplete Impl …` is perfectly satisfiable. So step-completeness cannot
imply `Sound` into an arbitrary `Spec`. `Boundary.lean:158–163` records this verbatim:

> "the original `sound_of_step_complete` / `step_complete_of_sound` below (bisimulation to a
> free `Spec` parameter) are **false as stated** — with `Spec.Carrier = Empty`, `Sound Impl
> Spec x` is uninhabited while `StepComplete` holds (machine-checked)."

The same defect recurs and is **re-refuted** twice more, as a proved negative:
- `Hyperedge.hyperedge_sound_bisim_ill_posed` (`Hyperedge.lean:433`, PROVED) refutes the N-ary
  `family_joint_sound` shape `Sound (J.cell i) (Spec i) (b.pre i)` at `Spec () = Empty`.
- `JointViaHyper.lean:10–11` and `JointTurn.lean:451–457` document the same and route around it.

> **Tag: ASPIRATIONAL→retired.** The `▶`-guarded-bisimulation-to-a-free-Spec keystone is the
> one piece of categorical vocabulary that *over-promised* and was caught. It is now neither in
> the codebase nor claimed. This is the cleanest example in the corpus of category-language
> being held to a theorem and failing — and being downgraded rather than faked.

### 3.2 What replaced it — REAL, two pieces

**(a) The safety-invariant keystone — `stepComplete_preserves` (`Boundary.lean:177`, PROVED).**
The well-posed content: a state-predicate `Good` preserved by every `StepInv`-respecting
transition holds along the *entire* execution (a `Run` of the induced transition system). This
is the honest "step-completeness buys soundness," stated as a safety invariant, proved via
`Execution.invariant_run`. No free `Spec`, no `Empty` trap.

**(b) The genuine bisimulation, for a CONCRETE cell — `livingCell_sound` (`Exec/Cell.lean:102`,
PROVED).** This is the keystone REORIENT §5 named as the standing OPEN, **now closed**:
- `livingCell : TurnCoalg ℤ Turn` (`:42`) — carrier `ChainedState`, `obs = total kernel`,
  `next = cexec-or-self-loop` (a real Moore coalgebra, fail-closed self-loop on rejected input).
- `conservationOracle : TurnCoalg ℤ Turn` (`:52`) — carrier `ℤ`, `step v = (v, fun _ => v)` — a
  genuine **non-degenerate** oracle (NOT the `Empty` trick), the conserved-balance reference.
- `bisim_of_oracle` (`:67`, PROVED) — the well-posed `sound_of_step_complete`: given a decode
  map commuting with `obs` (`h_obs`) and with transition (`h_step`), `Impl` is bisimilar to
  `Spec` from every state. The witness relation is `R a b := b = oracle a`.
- `cell_h_step` (`:88`) — "this is exactly where step-completeness lands": the conservation
  conjunct of `cexec_attests` is what makes the oracle commute with the turn.
- `livingCell_sound` (`:102`) — the running cell is bisimilar to its conservation oracle from
  every state: its observable behaviour **never drifts from conservation over unbounded time**.

> **Tag: REAL.** The `▶`-guarded bisimulation, *with a concrete non-degenerate oracle*, is now
> proved. The honest difference from the aspiration: it is bisimulation to a *specific decode-
> image oracle* (`bisim_of_oracle` requires the bridge), not the unconditional "bisimilar to
> some Spec," and the `Obs` tracked is the conserved balance, not the full PI surface. This is
> exactly the move `STUDY-lean4-coinduction §3.2/§4.4.1` prescribed.

### 3.3 The `▶` ("later") guard itself — DECORATIVE-as-guard, REAL-as-position-marker

`Boundary.lean:103`: `def Later (Q : Prop) : Prop := Q` — the guard is the **identity on
Prop**. The `step_rel` field of `IsBisim` (`:123`) places the recursive occurrence *under*
`Later`, and `BoundaryRespecting.closed` (`:239`) likewise. But because `Later = id`, the guard
**enforces nothing**: it is documentation of *where* the tail-recursion recurs, not a
productivity check.

`STUDY-lean4-coinduction §2.4/§4.2.1` is candid: "`Later = id` makes the guard documentation,
not enforcement … the metatheory does **not** independently *check* productivity — it *assumes*
the impl's chain is well-formed and pushes the real content into `StepComplete`/`chainLink`."
The hash-chain (`previous_receipt_hash`) is the *operational* "head now / tail later" witness;
in the metatheory it lives in the `chainLink` conjunct of `StepInv`, not in `Later`.

> **Tag: DECORATIVE** for `▶`/`Later` *as a guarded-type-theory productivity modality*: it buys
> no theorem (it is `id`). To become REAL it would have to be the step-indexed `LaterIdx`
> (`STUDY §2.4 option 2`) or a genuine `▷` from a guarded backend, and a theorem would have to
> *use* the step-index to establish productivity the kernel can't. Note `ObsBisim`
> (`CoinductiveAdversary.lean:113`) is the place where productivity is *real* — but there it is
> the native `coinductive`'s guardedness checker (the `+1` schedule tick guards the recursive
> occurrence, `:118`), not `Later`.
>
> **Tag: REAL** for the *position* discipline: typing the recursive occurrence under `Later`
> correctly marks it as the "tail," and the native `ObsBisim` makes the guardedness genuine.

---

## 4. Step-completeness as contractivity / the "drifting future" — REAL-as-premise

The design's deepest coalgebra insight (`cand-A §4`, `decisions`-equivalent, `STUDY §0`): under
coinduction a **non-contractive step** — one that locally type-checks while leaking `Σ_k` — has
*unbounded* consequence; the chain corecurses forever, drifting. "The guard `▶` buys
productivity, not soundness; soundness needs the step to be *contractive in `StepInv`*."

The Lean encodes contractivity as **`StepComplete`** = every reachable transition attests the
full `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` (`Boundary.lean:150`,
building on `StepInv` at `:140`). And it is genuinely load-bearing:

- `stepComplete_preserves` (`:177`) **requires** `StepComplete` as a hypothesis (no drift along
  the whole run).
- `cell_h_step`/`livingCell_sound` (`Exec/Cell.lean:88,102`) route the **conservation conjunct**
  of `cexec_attests` into the bisimulation — i.e. contractivity-in-`Conservation` is *exactly*
  what makes the oracle commute and the bisimulation hold.
- `stepComplete_carries_infinite` (`CoinductiveAdversary.lean:227`, PROVED) carries any
  `StepInv`-preserved `Good` along an **unbounded** adversarial schedule — "no drifting future
  across the unbounded interleaving." This is the coalgebra's distinctive risk discharged at the
  infinite-time scale.

> **Tag: REAL.** "Step-completeness = the well-definedness/productivity condition of the
> infinite unfold" is faithfully realized: it is the premise of every no-drift theorem, and the
> infinite-schedule version proves the drift is excluded forever. The "drifting future as a
> non-contractive infinite coherence" is the correct intuition and the Lean cashes it as the
> `StepComplete` hypothesis — though note the *productivity* half lives in the native `ObsBisim`
> coinduction, while the *soundness* half lives in `StepComplete`; the design's claim that the
> guard and step-completeness are different jobs is borne out exactly.

**Caveat (the honest residue, `cand-A §9.1`):** step-completeness is proved-by-construction for
the *Lean* cell (`cexec_attests`), and the soundness theorems are *conditional on it*. Whether
the *running Rust/circuit* AIR is step-complete (all four conjuncts in-circuit) is the impl
audit, not a Lean theorem. The coalgebra is "less forgiving of a partial proof than a chain
would be" — a real architectural fact, not a metatheory gap.

---

## 5. The comonad / runtime-character (checkpoint / restore / replay / time-travel) — partly REAL, "anamorphism re-seed" DECORATIVE

`cand-A §5` claims checkpoint/restore/replay/time-travel are *theorems*, definitional
consequences of "(codata + retained log + rollback-handler turn)", with checkpoint = "name a
point in the unfold", restore = "re-seed the anamorphism", time-travel = "fork the unfold".

**What the Lean proves (`Exec/Cell.lean:117–`):**
- `Snapshot` (`:122`) — a genuine serialized-snapshot structure (records `headObs` + `kernel`).
- `restore_snapshot : restore (snapshot s) = s` (`:144`, PROVED by `rfl`) — round-trip.
- `restore_snapshot_obs` (`:149`, PROVED) — the badge survives the round-trip.
- `replay_deterministic` (`:155`) — replay is deterministic.
- The file's own historical note (`:113`) is important: "an earlier version made `checkpoint :=
  id` and proved `restore (checkpoint s) = s` by `rfl` … both `id`-identities advertised as the
  time-travel payoff" — and it was de-vacuified into a real `Snapshot` carrier.

> **Tag: REAL** for checkpoint/restore/replay as *theorems about a concrete snapshot carrier* —
> they say something the type system does not already force (the de-vacuified version), and they
> are honest about a snapshot that records the observable badge.
>
> **Tag: DECORATIVE** for "restore = **re-seed the anamorphism**" / "time-travel = **fork the
> unfold of `νF`**." There is no anamorphism and no `νF` (§2), so these are not literal
> anamorphism operations — they are operations on the concrete `ChainedState` carrier. The
> *comonadic* framing (codata + extract/duplicate giving checkpoint/restore for free) buys no
> theorem: there is no `Comonad` instance, no `extract`/`duplicate`, no proof that restore is a
> comonad counit. To become REAL the comonad claim would need a `Comonad` (or coalgebra-of-a-
> comonad) instance with the laws, and checkpoint/restore proved as its structure maps. As
> built, they are good *concrete* theorems wearing comonadic *vocabulary*. **Time-travel/fork
> over `νF` is the most aspirational of these — it would need the codata value to exist first.**

---

## 6. The cross-cell ⊗ and the "tensor non-finality" finding — corrected, and what survives is REAL

`study-category §1` called tensor non-finality "the single most important coherence-finding" —
`νF₁ ⊗ νF₂` is *not* the final coalgebra of the product behaviour, so cross-cell soundness is
irreducible to per-cell. The Lean's relationship to that claim is itself a correction worth
recording precisely.

### 6.1 The `tensor_not_final` claim was MIS-STATED and is corrected to `binding_is_proper`

`JointTurn.lean:320–333` (the `binding_is_proper` doc) carries the audit:

> "*Correction (audit):* the earlier `tensor_not_final` ('νF₁ ⊗ νF₂ is not final') was
> **mis-stated** — the product of two final coalgebras IS final for the product functor, so that
> claim is false. The true, soundness-critical content is a **proper-subobject** fact:
> `JointBinding` (CG-2 ⊗ CG-5) is a *non-trivial constraint*, so the joint-admissible
> configurations are a proper **equalizer subobject** of the product carrier."

This is a sharp categorical correction: the product of final coalgebras *is* final for the
product functor (`ν(F₁×F₂) ≅ νF₁ × νF₂`), so "tensor non-finality" as literally stated is false.
The real obstruction is that the **binding carves a proper subobject** of the product carrier.

### 6.2 What is REAL here

- `binding_is_proper` (`JointTurn.lean:333`, PROVED): two one-state cells each moving a
  half-edge of `1 : ℕ`, CG-5 sum `1+1 = 2 ≠ 0` — a product config that is **not** `JointAdmissible`.
- `joint_sound` (`JointTurn.lean:230`, PROVED): cross-cell safety, **with the `JointBinding`
  (CG-2 ⊗ CG-5) as an explicit HYPOTHESIS**, reduced to `stepComplete_preserves` on the product
  coalgebra `jointCoalg` (`:158`).
- `joint_sound_needs_binding` (`JointTurn.lean:271`, PROVED): no "both step-complete ⇒
  joint-admissible everywhere" theorem can hold — the binding is load-bearing.
- The **hyperedge upgrade** (`Hyperedge.lean`): the N-ary binding is ONE wide-pullback apex
  `tid` + a single `Finset.sum = 0` (`Hyperedge:80,99`), `legs_agree` is a *theorem*
  (`:111`, the `O(N²)` pairwise agreements collapse), `hyperedge_sound` is PROVED axiom-clean
  (`:374`), and `hyper_not_all_admissible` (`:505`, PROVED) is the general-`ι` proper-subobject
  witness. `joint_via_hyperedge` (`JointViaHyper.lean:75`) reads off the N-ary keystone as a
  corollary; the binary `JointBinding` is the `Fin 2` slice (`Hyperedge.toJointBinding:213`).

> **Tag: REAL** for "cross-cell joint-soundness is irreducible to per-cell ∧ per-cell, because
> the binding is a proper equalizer subobject" (`binding_is_proper`, `hyper_not_all_admissible`,
> `*_needs_binding`). The category *earns its keep* by forbidding the wrong factoring — exactly
> `study-category §1.3`'s thesis, now PROVED.
>
> **Tag: DECORATIVE→corrected** for the original slogan "`νF₁ ⊗ νF₂` is not final": the Lean
> audit shows it is *false as a finality statement*. The honest content is the proper-subobject
> fact, and the codebase corrected the naming. (`study-category.md` itself flagged "⊗ of
> coalgebras" as "the load-bearing lie to retire" — the Lean retired it correctly.)
>
> **Tag: REAL** for `jointCoalg`/`hyperCoalg` as honest **product coalgebras** (`JointTurn:158`,
> `Hyperedge:319`) and `JointAdmissible`/`HyperAdmissible` as the **equalizer/wide-pullback
> subobjects** they carve (`JointTurn:170`, `Hyperedge:151`). These are genuine categorical
> objects with genuine theorems, not decoration.

---

## 7. The conservation "functor `Σ`" and the camera `▶` — `Σ`-functor DECORATIVE, camera-guard ASPIRATIONAL

### 7.1 `Σ` as a strong monoidal functor — DECORATIVE (the content is a monoid-hom)

`Core.lean` encodes conservation as `Conservation.count : Cell → M` plus `unit_zero`
(`count I = 0`, `:124`) and `tensor_add` (`count (A⊗B) = count A + count B`, `:132`). The header
(`Core.lean:9–13`) and `Conservation`'s own doc (`:126–131`) are explicit:

> "the 'strong monoidal functor' packaging is *decorative* — its target is discrete on objects,
> so the functor laws collapse to the monoid-hom + invariance."

The real obligation is `conservation_step` (`:154`, the one **stated-`sorry` PRIMITIVE** — the
operational model must discharge Law 1's balance) plus the *proved* corollaries
`conservation_ordinary` (`:166`), `mint_delta`/`burn_delta` (`:176,187`), and the genuinely
nice `withholding_no_free_copy` (`:209`, PROVED): a conservation-respecting comonoid copy
`Δ : A → A ⊗ A` forces `count A = 0` in a cancellative monoid — *no free copy*, comonoid
coherence as a conservation constraint.

> **Tag: DECORATIVE** for "`Σ` is a strong monoidal *functor*": the functoriality is
> vacuous-on-a-discrete-target; the load-bearing object is the **monoid homomorphism**
> (`unit_zero` + `tensor_add`) plus invariance on ordinary turns. (Matches `study-category §2`
> exactly: HOLD as monoid-hom, functor dressing decorative.)
>
> **Tag: REAL** for the monoid-hom + the no-free-copy law (`withholding_no_free_copy`,
> `:209`) — comonoid-no-`Δ` as a *proved* conservation constraint, the genuinely categorical
> content. And `TurnCat` (`Core.lean:85`) is honestly an *unfilled existence obligation* (a
> `class` whose `Category`/`MonoidalCategory`/`SymmetricCategory` instances are TODO) — so the
> SMC structure itself is **ASPIRATIONAL** (declared, not instantiated); the measure-level
> shadow (`tensor`/`unit`) is what carries the real work.

### 7.2 The camera and the `▶`-as-step-index — REAL camera, ASPIRATIONAL guarded-fixpoint

`Resource.lean` builds a discrete resource algebra (Iris camera): `ResourceAlgebra` (`:71`) with
`op`/`valid`/`core` and the three core laws, the frame-preserving update `Fpu` (`:103`,
`Fpu.refl`/`Fpu.trans` PROVED), and three real instances — `ℕ` (`:127`), `Excl` (the NFT/linear
camera, with `excl_no_dup` PROVED `:185`), and `Auth` (the authoritative↔fragment camera,
`conservation_is_fpu` PROVED `:296`). The unification `ConfinesAuthority := Fpu` (`:319`) makes
"authority never grows" and "conservation" *one definition*.

The crucial coalgebra tie is `Resource.lean:50–55`:

> "When dregg2 needs [higher-order/recursive resources], the camera's step-index should be the
> SAME `▶` ('later') as `Boundary.lean`'s guard — exactly how Iris builds `iProp` as a guarded
> fixpoint over cameras. Until then the discrete RA is the canonical tier."

> **Tag: REAL** for the camera tier (the RA class, the three instances, `Fpu`, the
> conservation=authority unification — all PROVED with only one localized `sorry` for the `Auth`
> validity laws that's actually discharged in-module). This is the cleanest "conservation and
> authority are one law" content.
>
> **Tag: ASPIRATIONAL** for the **guarded fixpoint over cameras** (Iris `iProp` as `▶`-fixpoint,
> the higher-order/recursive-resource tier where the camera's step-index = `Boundary`'s `▶`).
> This is the place the design *says* the comonadic/guarded-recursion story would unify the
> coalgebra guard and the resource step-index — but it is explicitly "until then," unbuilt: no
> step-indexed OFE, no non-expansive `op`, no guarded `iProp`. It is the single most promising
> unrealized categorical unification in the lens (the `▶` that types the cell's tail *and* the
> camera's recursive resource would be literally the same modality).

---

## 8. The vat-boundary functor `Φ` (caps→keys) — ASPIRATIONAL (the one real `sorry`)

`Spec/VatBoundary.lean` is where the coalgebra meets authority: `Φ` (`Phi`, `:106`) crosses a
positional cap to the witnessed epistemic demand it becomes off-vat. The named loss is REAL and
PROVED:
- `cross_vat_needs_witness` (`:138`, PROVED) — intra positional / cross witnessed.
- `phi_drops_confinement` (`:202`, PROVED) — permission survives, authority does not.
- `forwarded_cap_is_revocable` (`:240`), `revocable_iff_not_authority` (`:251`),
  `macaroon_does_not_cross_phi` / `biscuit_crosses_phi` / `phi_domain_is_exactly_biscuit`
  (`:281,289,296`), `phi_composes_with_attenuation` (`:314`) — all PROVED, all
  `#assert_axioms`-clean (`:465–474`).

But the **functoriality** of `Φ` is exactly the one genuine proof-body `sorry`:
- `PhiFunctorial` (`:356`) states the functor laws (preserves-id, preserves-comp, lossy-on-
  confinement = non-faithful).
- `phi_functorial` (`:392`) — **`sorry` at `:401`** (confirmed: the only proof-body `sorry`
  in all of this lens's files). Its doc (`:380–391`) is precise about what's open: "the
  *categorical coherence* tying the positional graph dynamics … to the epistemic discharge
  composition … into identity/composition-preserving functor laws SIMULTANEOUSLY with the
  lossiness witness … over an ABSTRACT `Verifiable`."
- `phi_functorial_concrete` (`:441`, PROVED, `#assert_axioms`-checked `:456`) — a concrete
  non-degenerate instance proving the three laws ARE inhabited and locating the named loss.

> **Tag: ASPIRATIONAL** for "the vat boundary is a **functor** caps→keys": this is precisely the
> brief's example — `phi_functorial` is a by-design `sorry`, so Φ-being-a-functor is *aspired*,
> not proved. To become REAL it needs the full two-category bridge (positional authority category
> ↦ epistemic authority category, id/composition preservation + the lossiness witness for one
> `Phi stmtOf` over an abstract `Verifiable`). The concrete witness shows it's *consistent*, not
> *general*.
>
> **Tag: REAL** for Φ's **action on objects, its named loss, its domain, and its monotonicity**
> — these are the genuinely-load-bearing facts (permission survives ∧ authority does not;
> biscuits cross, macaroons don't; no amplification), all proved.

This is the categorical dual to §3.1: where `sound_of_step_complete` was an *over-claim caught
and retired*, `phi_functorial` is an *under-delivered claim honestly marked `sorry`* — the same
discipline, two faces.

---

## 9. The lens-specific answer: what is an INFINITY-CELL, and a HIGHER-ORDER cell / turn?

The brief asks me to answer these *through the coalgebra lens*. Here is the honest answer,
grounded in what is and isn't proved.

### 9.1 The COHERENCE axis — a 2-cell as a bisimulation/rewrite between turn-executions

In the coalgebra reading there is a natural tower:

- **0-cell:** a *state* (a point `x : Carrier` of the coalgebra).
- **1-cell:** a *turn-execution* — the edge `x ↦ next x t` (the action of `step`).
- **2-cell:** a **coherence between two turn-executions** — and *this is where the Lean has real
  content*. The right notion of a 2-cell is **a bisimulation (or a provable rewrite) identifying
  two executions**. There are two genuine instances:
  - **The up-to-commutation closure `commClo` in `CoinductiveAdversary.lean:394`.** This is
    *literally* a 2-cell: it says "two diagonal points are related if reachable from a related
    pair by **rewriting either endpoint along a provable state-equality** (the finite
    commutation: two disjoint commits produce equal successor states)." That rewrite-between-
    executions is a 2-morphism, and `commClo_compatible` (`:413`, PROVED) is the coherence law
    that makes it sound to apply *under* the greatest fixpoint.
  - **The `Hyperedge.legs_agree` apex (`Hyperedge.lean:111`)** is a degenerate 2-cell: all N
    incidence-executions are coherent because they factor through one `tid`.

> **So a 2-cell of the dregg interaction tower = a bisimulation-up-to (a provable rewrite)
> between turn-executions, and it is REAL** — `commClo` + `commClo_compatible` are proved
> (`CoinductiveAdversary.lean:394,413`). This is the genuine higher-categorical content in the
> codebase, and it is exactly the **up-to-context / companion** machinery from `Paco`
> (`Paco/Companion.lean:33` `companion = cpn`, `companion_compat:54` PROVED).

### 9.2 Step-completeness as what makes the tower WELL-DEFINED

The ∞-tower of a coalgebra is well-defined iff the unfold is *productive* (each level
determined by the previous). In dregg this productivity is **step-completeness**: a
non-contractive step makes the tower drift (the "drifting future"). The Lean realizes "the tower
is well-defined" as:
- `obsBisim_traj_of_bisim` (`CoinductiveAdversary.lean:166`, PROVED) — along *any* infinite
  schedule, related states stay `ObsBisim` *forever* (the whole tower coheres);
- `stepComplete_carries_infinite` (`:227`, PROVED) — and no safety predicate drifts.
- `obsBisim_of_uptoComm` (`:436`, PROVED) — the GENERAL case: the tower is derivable *up to* the
  2-cell closure `commClo`, threaded through `gpaco_clo`/`gpaco_clo_final`. This is the
  ∞-coherence (bisimulation up to a tower of commutations) made a theorem.

> **REAL.** Step-completeness is exactly "what makes the (∞-)tower well-defined" in the sense
> the Lean can state: the productive, non-drifting greatest fixpoint. The native `coinductive
> ObsBisim` + the Paco `gupaco` up-to-2-cell closure are the genuine ∞-categorical engine.

### 9.3 What an INFINITY-CELL *is* (the lens answer)

**Honest answer: an "∞-cell" in dregg, through the coalgebra lens, is a coalgebra carrier
together with its productive, step-complete bisimulation tower — but the *finality* that would
make it the canonical such object is aspirational, and the higher coherences are real only up to
dimension 2.** Concretely:

- the **0/1 structure** (state + turn-execution) is REAL (`TurnCoalg`, `Exec/Cell.lean`);
- the **bisimulation** (the relation that would be "equality on `νF`") is REAL as a relational
  gfp and as native `ObsBisim`, but **not** as equality-on-a-final-object (no `νF`, §2);
- the **2-cells** (rewrites/bisimulations-up-to between executions) are REAL via `commClo` /
  the Paco companion;
- **3-cells and above** (coherences between coherences) are **DECORATIVE/UNBUILT** — there is no
  proved associativity/interchange of the `commClo` rewrites, no simplicial-identity layer
  (`DREGG4-HYPERSYSTEM §4.3` is explicit: "there is no proved simplicial-identity layer," and a
  free higher filler "would be unsound").

So the ∞-cell is, today, a **2-truncated** object: a coalgebra with a sound bisimulation-up-to-
2-cells. The full ∞-groupoid/∞-category tower is **DECORATIVE until each higher cell carries its
own binding** — `DREGG4-HYPERSYSTEM §4.4`'s OBSTRUCTION 1: "a 'full simplicial object' with free
higher fillers is *unsound*; the only sound simplicial object is one where the filler of each
n-simplex is a `Hyperedge` carrying its CG-2 ⊗ CG-5" (grounded `hyper_not_all_admissible`,
`Hyperedge.lean:505`). The tower is a **fibration over the bindings**, never a free complex.

### 9.4 What a HIGHER-ORDER cell / HIGHER-ORDER turn *is*

Two distinct readings, both grounded:

**(a) Higher-order turn = the rollback handler (the handler-turn).** `cand-A §2.2` /
`GLOSSARY: turn` / `CARRY-FORWARD §0`: a turn is *simultaneously* the coalgebra step, the
rollback handler (holds outgoing effects until commit; commit = replay-held-log + advance-`▶` +
emit-witness; abort = discard = conservation-preserving refund), and the deferred-prover trigger.
A *higher-order* turn is one whose payload is itself a turn/handler — e.g. the **rollback-handler
that re-seeds an earlier snapshot** (time-travel) or the **cross-cell forest node that delegates
an attenuated cap to a child subtree** (`Exec/CrossCellForest.lean`).

> **Partly REAL.** The delegation-of-a-subtree-under-a-derived-cap *is* a higher-order turn and
> it is proved well-behaved: `crossForest_no_amplify` (`CrossCellForest.lean:217`, PROVED) —
> every cross-cell delegation edge is non-amplifying (Granovetter across cells, fully general
> over the tree); `crossForest_conserves` (`:241`, PROVED, binding-carried). The handler/await
> *family* (zkpromise / discharge / intent / settled-call-return, `GLOSSARY: await family`) is
> the design's account of higher-order turns; its algebraic-effects framing ("continuations are
> the one non-algebraic effect, so the substrate is two layers") is **DECORATIVE** in this lens
> (no `Comonad`/`Handler`-algebra instance proved) — but the *delegation* face is REAL.

**(b) Higher-order cell = a cell whose state holds an invariant *about another cell* (a recursive
resource).** This is the Iris higher-order-camera reading (`Resource.lean:50–55`): a cap that
stores an invariant about another cell, or a resource living *inside* the coinductive `νF`. This
is the unification point where the camera's `▶` step-index = `Boundary`'s `▶` guard.

> **ASPIRATIONAL.** This is the explicitly-unbuilt tier (the guarded `iProp`-over-cameras, §7.2).
> A higher-order cell — one whose `Obs`/state quantifies over other cells' invariants — needs the
> guarded fixpoint that does not yet exist. It is the cleanest statement of "what dregg's
> coalgebra would have to grow to host genuine higher-order capability."

**Reconciliation:** in the coalgebra lens, *higher-order turn* (handler/delegation, partly REAL)
and *higher-order cell* (recursive resource, ASPIRATIONAL) are the two faces of the same future
unification: the `▶` that guards the cell's tail is the same `▶` that would index a recursive
resource a higher-order cell stores. The protocol-cell / choreography layer (`GLOSSARY:
coordination layer`, `cand-D`) is the "a cell coordinating cells" instance — a higher-order cell
whose `CellProgram` *is* a global choreography type — and it rests on open theorems (REORIENT §5
lists it last). So: the **handler-turn is the higher-order turn that exists; the recursive-
resource cell is the higher-order cell that is aspired.**

---

## 10. REAL / DECORATIVE / ASPIRATIONAL — the lens table

| # | Structural claim | Tag | Grounding (`file:line`) | If not REAL: what it would have to prove |
|---|---|---|---|---|
| 1 | Behaviour functor `F X = Obs × (AdmTurn ⇒ X)`; cell = point of an `F`-coalgebra | **REAL** | `Boundary.F:66`, `TurnCoalg:74`, `Exec/Cell.livingCell:42` | — |
| 2 | The cell is the **FINAL** coalgebra `νF` (terminal universal property) | **ASPIRATIONAL** | no `νF`/`Cofix`/`MvQPF` in `Dregg2/`; `STUDY-coind §0` | register `F` as `MvQPF`, build `Cofix F`, prove unique anamorphism / `Cofix.bisim` |
| 3 | Bisimulation principle / relational gfp (`IsBisim`/`Sound`/`bisim_eq`/`sound_refl`) | **REAL** | `Boundary:117,130,203,211` | — |
| 4 | Native greatest-fixpoint bisimilarity over `νF` schedule (`ObsBisim` + `.coinduct`) | **REAL** | `CoinductiveAdversary:113,166` | — |
| 5 | `sound_of_step_complete` (step-complete ⇔ bisimilar-to-a-free-`Spec`) | **ASPIRATIONAL → retired (FALSE-as-stated)** | refuted `Spec=Empty`, `Boundary:158–163`; re-refuted `Hyperedge:433` | nothing — it is false; the honest replacements are #6/#7 |
| 6 | Step-completeness ⇒ whole-execution **safety** (`stepComplete_preserves`) | **REAL** | `Boundary:177` | — |
| 7 | The CONCRETE living cell is bisimilar to a non-degenerate conservation oracle | **REAL** | `Exec/Cell.bisim_of_oracle:67`, `livingCell_sound:102` | — |
| 8 | `▶`/`Later` as a guarded-type-theory **productivity** modality | **DECORATIVE** | `Boundary.Later:103` (`= id`) | step-indexed `LaterIdx` (`STUDY §2.4`) or a `▷` backend, with a theorem that *uses* the index |
| 9 | Step-completeness = contractivity / no "drifting future" (load-bearing premise) | **REAL** | `StepComplete:150`, `stepComplete_carries_infinite:227` | — |
| 10 | Checkpoint/restore/replay as theorems over a real snapshot carrier | **REAL** | `Exec/Cell:122,144,149,155` | — |
| 11 | restore = **anamorphism re-seed**; time-travel = **fork the unfold of `νF`**; cell = **comonad** | **DECORATIVE** | no anamorphism/`νF`/`Comonad` instance | build `νF`; a `Comonad` instance with laws; restore/fork as its structure maps |
| 12 | Cross-cell soundness irreducible: binding is a **proper equalizer/wide-pullback subobject** | **REAL** | `binding_is_proper:333`, `hyper_not_all_admissible:505`, `*_needs_binding` | — |
| 13 | "`νF₁ ⊗ νF₂` is not final" (the `tensor_not_final` slogan) | **DECORATIVE → corrected (false)** | `JointTurn:320–333` audit | nothing — product of finals IS final; correct content is #12 |
| 14 | `jointCoalg`/`hyperCoalg` product coalgebras; `JointAdmissible`/`HyperAdmissible` subobjects | **REAL** | `JointTurn:158,170`, `Hyperedge:319,151` | — |
| 15 | `Σ` (conservation) is a **strong monoidal functor** | **DECORATIVE** | `Core:9–13,126–131` (self-flagged) | a non-discrete target where functoriality-on-morphisms is non-vacuous (the design rejects this) |
| 16 | Conservation = monoid-hom + no-free-copy (comonoid-no-`Δ`) | **REAL** | `Core.withholding_no_free_copy:209`, `tensor_add:132` | — |
| 17 | `TurnCat` symmetric-monoidal category instance | **ASPIRATIONAL** | `Core.TurnCat:85` (TODO `class`, no instances) | discharge `Category`/`MonoidalCategory`/`SymmetricCategory Cell` |
| 18 | Camera tier: conservation = authority = one FPU law | **REAL** | `Resource.Fpu:103`, `conservation_is_fpu:296`, `ConfinesAuthority:319` | — |
| 19 | Guarded fixpoint over cameras (`iProp`, camera-`▶` = `Boundary`-`▶`); higher-order cell | **ASPIRATIONAL** | `Resource:50–55` ("until then") | step-indexed OFE camera + guarded `iProp` fixpoint sharing `Boundary`'s `▶` |
| 20 | Vat boundary `Φ` is a **functor** caps→keys | **ASPIRATIONAL** | `phi_functorial` **`sorry`** `VatBoundary:401` | the full positional↦epistemic two-category bridge over abstract `Verifiable` (concrete witness exists `:441`) |
| 21 | Φ's named loss / domain / monotonicity (permission survives, authority doesn't) | **REAL** | `phi_drops_confinement:202`, `phi_domain_is_exactly_biscuit:296`, `phi_composes_with_attenuation:314` | — |
| 22 | 2-cell = bisimulation-up-to / provable rewrite between executions (the coherence axis) | **REAL** | `commClo:394` + `commClo_compatible:413`, Paco `companion_compat` | — |
| 23 | ∞-cell tower above dimension 2 (simplicial identities / free Kan fillers) | **DECORATIVE / UNSOUND-if-free** | `DREGG4-HYPERSYSTEM §4.3–4.4`; `hyper_not_all_admissible:505` | a simplicial object whose every n-face filler is a binding-carrying `Hyperedge` (fibration over bindings, not free) |
| 24 | Higher-order turn = handler / delegated-subtree-under-derived-cap | **REAL (delegation face)** | `CrossCellForest.crossForest_no_amplify:217`, `_conserves:241` | (algebraic-effects/comonad packaging of the await family is DECORATIVE: no handler-algebra instance) |

---

## 11. The single honest sentence

dregg2's cell is a **coalgebra with a proved bisimulation soundness for a concrete instance**,
not a **proved-final coalgebra**: `F`, `TurnCoalg`, `IsBisim`, the native `ObsBisim`,
`stepComplete_preserves`, and `livingCell_sound` are REAL; finality (`νF`, the terminal universal
property, the anamorphism), the `▶`-as-productivity-guard, the comonadic runtime, the `Σ`-functor
and `TurnCat` SMC, the guarded camera-fixpoint, and `Φ`-as-functor are the named aspirations and
decorations — and the coalgebra *earns its keep precisely where it is REAL*: it forbids the wrong
cross-cell factoring (`binding_is_proper`), forbids free copy (`withholding_no_free_copy`), and
turns "no drifting future" into a theorem conditional on step-completeness — while the higher
(∞-)coherence is real only up to the 2-cell `commClo`, and everything above is a fibration over
bindings the simplicial vocabulary must not pretend are free.

*( ˘▾˘ ) the egg is a coalgebra that dreams of being final — and is honest that it is not yet.*
