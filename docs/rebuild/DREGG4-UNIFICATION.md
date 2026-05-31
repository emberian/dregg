# DREGG4-UNIFICATION — the three-faced turn at its limit (galaxy-brain rebuild design)

> **What this is.** A READ-ONLY design exploration for **dregg4**, the advanced/generalized successor.
> No code changed. It takes the synthesis of this session — the **three-faced turn** (effects ⊕ caveats ⊕
> attestation) with **two dials** (disclosure: *what-is-revealed*; transferability: *to-whom-convincing*) —
> and pushes it to its maximal generality: *is there one turn-generator whose three faces are projections,
> subsuming the 54-effect VM + the ad-hoc token system + bespoke storage into one uniform algebra?*
>
> **Sources read in full this session and cited by `file:line`:** `REORIENT.md`,
> `CARRY-FORWARD-SYNTHESIS.md`, `GLOSSARY.md`, `EFFECT-ISA-DESIGN.md`, `GROUND-AUTH-ATTESTATION.md`,
> `GROUND-STORAGE-PROGRAMS.md`, `cand-A-vat-coalgebra.md`, `cand-B-witness-pca.md`,
> `cand-C-cap-distributed.md`, `cand-D-choreography.md`, plus the `pdfs/INDEX.md` clusters (coalgebra,
> algebraic effects, accumulation/folding, anonymous credentials, MPST/choreography, PCA, info-flow).
>
> **Discipline carried in (non-negotiable, from `REORIENT §6`):** crypto-soundness is *never* merged into
> the semantic law (the §8 rail); step-completeness is THE soundness question; no fake-to-pass; improve,
> don't degrade. Every "genuinely new" claim below is distinguished from a *rephrasing* of what exists.

---

## 0. The one-paragraph thesis

dregg has been built as an **effects machine** with auth and attestation bolted to its side. The session's
grounding shows that is a *projection mistake*: a turn is **one generator with three co-equal faces**
(`CARRY-FORWARD-SYNTHESIS §0`). dregg4's galaxy-brain rebuild is to make that literally true — to find the
**single coalgebraic generator** whose three faces (what the turn *does*, what it is *allowed* to do, what
it *emits*) are mathematical projections, parameterized by **two orthogonal dials** that today are pinned
or absent. The payoff is not "fewer effects." It is that **storage, advanced credentials, deniable
interaction, cross-chain bridging, and the whole token system stop being separate subsystems** and become
*instances* of one turn over a small core, narrowed by a caveat algebra, emitting an attestation whose
disclosure and transferability are chosen, not hardwired. The 54-effect VM + the macaroon/biscuit token
zoo + the bespoke `storage/` crate collapse into **one core + one algebra + one modal attestation lattice**.

---

## 1. The current sprawl, named precisely (so we know what we are collapsing)

Three independent sprawls, each grounded this session:

1. **Effect sprawl** — 54 selectors (`turn/src/action.rs:760`, `circuit/.../columns.rs:78`) that
   `EFFECT-ISA-DESIGN` shows are **~11 genuine shapes wearing ~50 names**: ≈24 of them are *one row*
   (`Meta.bind(domain_tag, hash)`) distinguished only by a constant (`EFFECT-ISA-DESIGN §S6`, `air.rs:909–1000`).
2. **Token/caveat sprawl** — a *parallel* authorization machine (macaroon HMAC chains, biscuit Ed25519
   chains, 3P discharge with ticket/VID, stealth one-time keys, StarkDelegation, credentials with selective
   disclosure + multi-show) living in `macaroon/`, `token/`, `credentials/`, `cell/src/stealth.rs`,
   `turn/src/executor/authorize.rs` — *separate* from the effect VM, and the **Lean is a fiction exactly
   here** (`GROUND-AUTH-ATTESTATION §1.6`: "no HMAC chain integrity," "3P discharge is a Bool flip,"
   "selective disclosure absent").
3. **Storage sprawl** — `storage/` (MerkleQueue, WAL, quota, erasure), `persist/` (redb), `rbg/vfs.rs`, and
   the `dregg-storage-templates/` migration. `GROUND-STORAGE §5` *already proves* storage is DSL-userspace
   over the effect core (every template is `SetField + EmitEvent + Transfer` under a `CellProgram`) — so
   this sprawl is *half-collapsed already*, and the residue (WAL durability) is honestly **below the ISA**.

**The unification claim of dregg4:** sprawls (1) and (2) are not two machines but **two faces of one turn**,
and (3) is **userspace over face (1)**. The current architecture pays for three machines; dregg4 pays for one.

---

## 2. The single generator — the turn as one coalgebraic object, three faces as projections

### 2.1 The functor, extended to carry all three faces

`cand-A §1.1` gives the cell as a point of the final coalgebra `νF`, `F X = Obs × (AdmissibleTurn ⇒ X)`.
That functor already *contains* the three faces — they were just not named as projections:

```
F X  =  Obs × (AdmissibleTurn ⇒ X)
        └┬┘    └──────┬───────┘
   ATTESTATION    the arrow's DOMAIN (CAVEATS) and CODOMAIN-action (EFFECTS)
```

- **EFFECTS = the codomain action.** `AdmissibleTurn ⇒ X` *maps to the successor cell* — the state
  transition. This is face 1, the `apply_*` mutation (`turn/src/executor/apply.rs`), the `cexec` of the
  step-complete spine (`Exec/StepComplete.lean: cexec_attests`).
- **CAVEATS = the domain restriction.** `AdmissibleTurn` is a *dependent, witness-guarded* alphabet
  (`cand-A §1.1`): a turn is in the domain iff it carries a witness discharging admissibility. **The caveat
  face IS the predicate that carves `AdmissibleTurn` out of `AllTurn`.** This is exactly the `CellProgram`
  as "the admissibility filter — which turns are admissible" (`GLOSSARY: CellProgram`, `cell/src/program.rs:53`).
- **ATTESTATION = `Obs`.** The badge — `(permitted) ∧ (effects-committed)` (`GLOSSARY: the badge`). The
  `WitnessedReceipt` (`turn/src/witnessed_receipt.rs:245`).

So the three faces are **literally** the three components of the coalgebra structure map `c : X → F X`:
*domain of the arrow* (caveats), *action of the arrow* (effects), *output component* (attestation). This is
not a metaphor — it is the decomposition of `F`. **dregg4's central rebuild is to treat `c` as the only
primitive and derive the three subsystems as its projections**, instead of building three subsystems and
hoping they agree.

### 2.2 Why this is genuinely-new and not a rephrasing

`CARRY-FORWARD-SYNTHESIS §0` *names* the three faces; `cand-A` *names* the coalgebra. **Neither connects
them.** The new content here is the identification:

| Face | Coalgebra projection | Today (separate machine) | dregg4 (one projection) |
|---|---|---|---|
| effects | codomain action `⇒ X` | 54-selector EffectVmAir | small core ISA (the action's generators) |
| caveats | domain of the dependent arrow | macaroon/biscuit/discharge/credentials, *outside* the VM | the **predicate that defines `AdmissibleTurn`** |
| attestation | `Obs` component | WitnessedReceipt, pinned non-repudiable | a **modal `Obs`** indexed by the two dials |

The repudiation gap (`GROUND-AUTH §2`) is then *not* a missing feature — it is the observation that **`Obs`
has been built as a single global type** when the coalgebra permits it to be **a modal/indexed object**
(§4). The whole of Part 2 of `GROUND-AUTH` is "we pinned the `Obs` projection at one point of a lattice it
could range over." That reframing is the galaxy-brain move.

---

## 3. The unified type/algebra (the sketch)

Here is the maximally-general turn type. It is one generator; the three faces are its three fields; the two
dials parameterize the attestation field. (Lean-ish; not committed code.)

```
-- The TWO DIALS, first-class (today: disclosure is a per-field enum; transferability does not exist)
inductive Disclosure | acceptanceOnly | selective (reveal : Finset FieldId) | full
inductive Transferability | public | designated (verifier : VerifierId) | deniable (ring : Finset Authorizer)

-- FACE 1 (EFFECTS): the SMALL CORE — the action's generators (EFFECT-ISA-DESIGN §5, ~11 shapes)
inductive Core
  | balanceMove (asset : AssetClass) (from to : Option CellRef) (δ : Int)   -- C1, per-ASSET (the #1 gap)
  | supplyAdjust (asset : AssetClass) (cell : CellRef) (δ : Int) (disclosed : Bool)   -- C2
  | cellCreate (seed : CellSeed)                                            -- C3 (object generation = ana-seed)
  | capEdge (op : {add,remove,narrow}) (e : CapEdge)                        -- C4 (authority graph)
  | capExercise (slot : Slot) (inner : List Core)                          -- C5 (the eval map; recursive)
  | fieldWrite (idx : FieldId) (v : Value)                                  -- C6
  | metaBind (tag : DomainTag) (h : Hash)                                   -- C7 (subsumes ~24 selectors)
  | lifecycle (phase : Phase)                                              -- C8 (guarded FSM)
  | sideLock (rec : HoldingRecord) | sideSettle (id : LockId) (p : Predicate)  -- C9/C10
  | noteInsert (commit : Commit) | nullifierSpend (n : Nullifier) (w : Witness) -- C11/C12
  | nonceTick                                                              -- C13
  -- NEW CORE the architecture demands (EFFECT-ISA §3 ranked):
  | boundHalfEdge (peer : CellRef) (asset : AssetClass) (δ : Int) (exists : Witness)  -- CG-5 cross-cell
  | boundaryExport (slot : Slot) (φ : Attenuation) | boundaryImport (key : KeyCap)    -- ρ_out / ρ_in
  | returnProject (Δobs : ObsDelta) | awaitSettle (on : Predicate)         -- the 2nd observation / zkRPC
  | forkSpan (at : ReceiptId)                                              -- time-travel primitive

-- FACE 2 (CAVEATS): the ALGEBRA that narrows AdmissibleTurn (a bounded meet-semilattice / Heyting)
inductive Caveat
  | first (p : AuthContext → Bool)         -- macaroon first-party: a narrowing predicate
  | thirdParty (gw : GatewayId) (cid vid : Ciphertext)   -- 3P discharge: ENCRYPTED ticket/VID (real crypto)
  | bindParent (tailHash : Hash)           -- bind-to-parent (the chain-integrity binding)
  | predicate (k : WitnessedKind) (stmt : Stmt)   -- Gte/Lte/InRange/BlindedSet (selective-disclosure proofs)
structure CaveatChain where
  root  : KeyRef                            -- biscuit (pubkey) | macaroon (HMAC) | sel4-reflected
  tail  : Hash                              -- Tᵢ = H(Tᵢ₋₁, encode(Cᵢ))  -- THE chain integrity, modeled
  links : List Caveat
-- meet (attenuation): chain extension is append-only, narrowing-ONLY (the keystone law)
def CaveatChain.attenuate (c : CaveatChain) (k : Caveat) : CaveatChain := ⟨c.root, H(c.tail, enc k), c.links ++ [k]⟩

-- FACE 3 (ATTESTATION): the MODAL Obs, indexed by the two dials (today: a single global type)
structure Attest where
  permitted : Proof                         -- de-jure: a CDT/caveat-chain derivation witness
  committed : ObsDelta                       -- de-facto: per-asset CONSERVATION_VECTOR + Obs advance
  disclosure : Disclosure                    -- WHAT is revealed
  transfer   : Transferability               -- TO WHOM it is convincing  ← the new axis

-- THE ONE TURN: one generator, three faces.
structure Turn where
  effects  : List Core                       -- face 1
  guard    : CaveatChain                      -- face 2 (defines membership in AdmissibleTurn)
  attest   : Disclosure × Transferability     -- face 3 dials (the Obs the commit emits is computed)
```

### 3.1 What collapses into uniformity (genuine collapse, not relabeling)

- **The token zoo → the caveat-chain algebra.** macaroon (`root = HMAC`), biscuit (`root = Ed25519`),
  sel4-reflected (`root = kernel handle`) are **one `CaveatChain` over three `KeyRef` roots** — exactly
  `cand-C §10`'s "the biscuit delegation graph ≡ the distributed CDT." The HMAC tail (`macaroon.rs:204-262`,
  today a `GROUND-AUTH §1.6` **overlook** in Lean) becomes the `tail` field; attenuation = `attenuate`,
  the one keystone law that *is* already proved (`Authority/Caveat.lean: attenuate_narrows`,
  `GROUND-AUTH §1.6` verdict **F**). 3P discharge stops being a `Bool` flip and becomes a `Caveat.thirdParty`
  carrying real ciphertext.
- **Storage → DSL-userspace over the core** (already shown, `GROUND-STORAGE §5`): every template is
  `fieldWrite + metaBind + balanceMove` under a `CellProgram`; the one primitive it needs (the
  holding-store) is `sideLock/sideSettle`, already in the core for escrow (FID-ESCROW).
- **The ~24 passthrough effects → one `metaBind(tag, hash)`** (`EFFECT-ISA §S6`/`§5 Phase R`).
- **checkpoint/restore/replay/time-travel → consequences of the codata + `forkSpan`** (`cand-A §5`), not
  effects.

### 3.2 What genuinely generalizes (new capability, not collapse)

- **Per-asset conservation** (`balanceMove`/`supplyAdjust` indexed by `AssetClass`) — the #1 soundness gap
  (`EFFECT-ISA §3.1`), today a single scalar `bal`.
- **The transferability dial** — *entirely* new (`GROUND-AUTH §2`: grep-confirmed zero deniability /
  designated-verifier anywhere). This is the deepest new axis (§4).
- **`returnProject` / `awaitSettle`** — turns are one-directional today (`EFFECT-ISA §3` #4); the second
  observation is the zkRPC face.
- **`forkSpan`** — `Spawn` is child-creation, not self-fork (`EFFECT-ISA §3` #5).

---

## 4. The two dials, taken to the limit (the heart of dregg4)

This is where the "maximally-general" claim earns its keep. The session found the system has **a disclosure
dial and a missing transferability dial** (`CARRY-FORWARD-SYNTHESIS §2 Face 3`). dregg4 makes both
first-class *and orthogonal*, and recognizes a **third latent dial**.

### 4.1 Dial 1 — Disclosure (what-is-revealed): already partly built, generalize it

Today: `FieldVisibility::{Public, Committed, SelectivelyDisclosable}` (`cell/src/state.rs:16-25`) +
presentation `disclose` (`presentation.rs:36`). The generalization: lift disclosure from a *per-field cell
attribute* to a **per-turn, per-face choice** — a turn may disclose its full effect list, only a commitment
to it, or a predicate over it (`Gte/Lte/InRange`, `presentation.rs:307-351`). The Lean must grow `VC.claim`
from "one opaque `Nat`" (`Credential.lean:153`, `GROUND-AUTH §1.6` **O**) to a *record with a revealed
subset + a Poseidon2 revealed-facts commitment*.

### 4.2 Dial 2 — Transferability (to-whom-convincing): the genuinely-new axis

`GROUND-AUTH §2.2(b)(c)` is conclusive: **zero deniability, zero designated-verifier, hardwired maximal
transferability.** dregg4 introduces `Transferability ∈ {public, designated(V), deniable(ring)}` as a
*modal index on `Obs`*. The three points:

- **`public`** — the existing universally-verifiable STARK/Ed25519 badge. **Required** on the consensus /
  proof-carrying-forest path (`GROUND-AUTH §2.3`: finality *depends* on transferability). This is the
  default and the only point the system has today.
- **`designated(V)`** — a designated-verifier ZK proof of `(turn authorized) ∨ (I know V's secret)`
  (`GROUND-AUTH §2.4(1)`). Convincing *only* to V (who knows they didn't forge it); worthless to relay.
- **`deniable(ring)`** — a ring/chameleon construction: "one of this set authorized; you can't prove which,
  and any of us could have forged it" (`GROUND-AUTH §2.4(3)`). The weakest, smallest delta — the BlindedSet
  anonymity-set machinery (`credentials/src/presentation.rs:176`) is the only stepping stone.

**The galaxy-brain unification:** these are *modalities on the same `Obs` object*. `Obs` becomes
`Obs[t : Transferability]`, and the soundness keystone `sound_of_step_complete` (`Boundary.lean`,
`cand-A §8`) lifts to a **verifier-indexed bisimulation**: `Discharged` stops being one universal predicate
and becomes `Discharged[V]` (`GROUND-AUTH §2.4` close: "indexing it by *which verifier* is convinced — a
genuinely new piece of theory"). The same turn, committed, can emit **two attestations at once**: a `public`
badge for the forest, and a `designated(V)` companion for the bilateral channel (`GROUND-AUTH §2.4` final:
"the consensus/forest path keeps the transferable badge; the new mode is a parallel private artifact").

### 4.3 Dial 3 — the LATENT third dial: Finality / agreement-strength (surfaced here, not yet considered)

There is a **third orthogonal axis hiding in plain sight**: the finality tier (`GLOSSARY: finality tiers`,
`cand-A §7`). Today it is a per-cell property, but structurally it is *exactly the same shape as the two
dials* — a choice on the attestation about **how strongly the world must agree this turn is the history**.
- disclosure = *what* the badge reveals,
- transferability = *to whom* the badge is convincing,
- **agreement = *how many* must concur it is canonical** (tier-1 causal → tier-4 constitutional).

Naming this as a *third dial on `Obs`* is, I believe, **new** — none of the candidates or grounding docs
put finality on the same footing as disclosure/transferability. It fits the model cleanly: the three dials
are the three honest judgements of `cand-A §1.3` / `GLOSSARY: three orthogonal judgements` re-projected onto
the attestation face (conservation lives in `committed`; ordering = the agreement dial; I-confluence = the
*eligibility precondition* for low agreement, just as it gates tier-1). **A turn's full attestation is a
point in a 3-cube** `Disclosure × Transferability × Agreement`, and the system today lives on one edge of it.

---

## 5. The deeper single generator — is there ONE object behind the three faces?

Yes, and it has a precise categorical name. The three faces are projections of a **dependent-lens / Moore
coalgebra**, and the cleaner statement is in terms of **comodels of an effect theory** (the algebraic-effects
line: `pdfs/handlers-of-algebraic-effects-plotkin-power`, `monadic-framework-delimited-continuations`).

### 5.1 The turn is a (dependent) lens; the three faces are its two halves + a guard

A lens `S ⇄ (P, U)` has a *get* (`S → P`, the view) and a *put* (`S × U → S`, the update). The turn is a
**dependent lens with a guarded domain**:
- **get = the attestation** (`Obs`, the view that crosses the boundary),
- **put = the effects** (the state update),
- **the domain of `put` = the caveats** (which updates are admissible).

This is *literally* the coalgebra of §2.1 written as a lens: `c : X → Obs × (AdmissibleTurn ⇒ X)` is
`(get, put-with-guarded-domain)`. The three faces are **not three things glued; they are the components of
one lens.** This matters because lenses *compose* — `capExercise` (`C5`, the recursive eval map,
`apply.rs:2441`) is exactly **lens composition**: exercising a cap runs an inner turn (inner lens) inside the
outer turn's put. The "recursive inner-effect gating" the circuit must bake (`EFFECT-ISA §C5`) is the
*compositional* structure of the lens, not a special case.

### 5.2 The comodel reading (the await/effect duality, made one)

`cand-A §3` already found the sharp fact: **continuations are the one non-algebraic effect** (Plotkin-Power),
so the await substrate is *two layers* (a gate-engine = algebraic handler + a delimited-continuation capture).
The deeper unification: **the cell is a comodel** (the dual of a model of an algebraic theory) of the effect
theory whose operations are the `Core` generators. A comodel is precisely "a machine that *responds* to
operations" — i.e., a coalgebra for the functor induced by the theory. So:
- the **effect signature** (the `Core` enum) is an *algebraic theory* `T`,
- the **cell** is a `T`-**comodel** (it *cohandles* effect operations against its state),
- the **turn** is one step of cohandling = the coalgebra structure map,
- the **caveats** are the *equations/guards* of the theory (which operation-applications are well-formed),
- the **attestation** is the *residual* the comodel emits (the Moore output).

This is the single object: **a guarded comodel of the effect theory, with a modal output.** It subsumes
cell-and-morphism (the `cand-A §1.2` "two co-primary primitives" tension) because a comodel *is* a coalgebra
— the morphism is the structure map, not a second object. (`pdfs/coalgebraic-semantics-silva` is the
grounding for "behaviour = coalgebra, equivalence = bisimulation.")

### 5.3 Why this is more than aesthetics (what it buys)

- **One soundness theorem, not three.** Instead of "effects conserve ∧ caveats narrow ∧ attestation binds"
  as three audits, soundness is *one* statement: the comodel is bisimilar to the golden-oracle comodel,
  with `StepInv` as the contractivity condition (`cand-A §4`). The three faces are conjuncts of `StepInv`
  *because* they are the three components of `c` — they cannot drift apart by construction.
- **Composition is free.** Lens/comodel composition gives `capExercise`, JointTurn (`⊗` of comodels,
  `GLOSSARY: JointTurn` — and the **non-finality of `νF₁⊗νF₂`** is exactly why the comodel tensor needs the
  CG-2⊗CG-5 binding as a hypothesis, `study-category`), and choreography projection (`cand-D`: projection is
  a functor `Choreo → ∏ Endpoint` — a *map of comodels*).
- **The dials are modalities on the output functor.** `Obs[t]` is `F` post-composed with a modality; the
  whole transferability theory becomes "lift the bisimulation through the modality," which is a known shape.

---

## 6. Advanced features / galaxy-brain rethinks for dregg4 (each with three-faced-turn fit + build cost)

Each entry: **what it is**, **the three-faced fit**, **new-vs-rephrase**, **build cost**.

### 6.1 The 3-cube attestation modality (`Disclosure × Transferability × Agreement`)
- **Fit:** the attestation face becomes a point in a 3-cube; the turn carries a target cube-point; commit
  emits the badge(s) realizing it. A single turn can emit *multiple* badges (public for the forest,
  designated for a peer).
- **New vs rephrase:** disclosure exists; transferability is **new** (`GROUND-AUTH §2`); putting agreement
  on the same footing as a *dial* is **new** (§4.3).
- **Build:** verifier-indexed `Discharged[V]` in Lean (the named-new theory); a DVZK companion circuit (OR
  of presentation-AIR + Schnorr-knowledge, `GROUND-AUTH §2.4(1)`); keep the public badge for finality.

### 6.2 Designated-verifier & deniable interaction as a parallel private artifact
- **Fit:** transferability=`designated/deniable` on the attestation; the *effects and caveats are unchanged*
  — only the `Obs` projection changes. This is the cleanest demonstration that the dials are orthogonal to
  the other two faces.
- **New vs rephrase:** **genuinely new capability** (zero exists, grep-confirmed `GROUND-AUTH §2.2(b)(c)`).
  This is the **repudiation gap** the session flagged as "a genuine privacy hole for an anonymous-collaboration OS."
- **Build:** DVZK circuit (medium); deniable MAC at the `captp/handoff.rs` layer for the live channel
  (`GROUND-AUTH §2.4(2)`); ring-signature companion reuses BlindedSet (`§2.4(3)`, smallest delta).

### 6.3 The caveat chain AS the CDT AS the strand log (one append-only object, three renderings)
- **Fit:** caveat face = the domain guard; `cand-C §10` establishes biscuit-chain ≡ CDT ≡ blocklace strand.
  dregg4 makes this *one type* (`CaveatChain` with a `KeyRef` root) rather than three crates
  (`macaroon/`, `token/`, the CDT in `cell/`).
- **New vs rephrase:** mostly **collapse** (the identity is known), but **modeling the HMAC tail integrity**
  is new in Lean (today an unflagged §8 hole, `GROUND-AUTH §1.6` #1).
- **Build:** add `tail : Hash` + the `Tᵢ = H(Tᵢ₋₁, Cᵢ)` law; prove "an adversary cannot *remove* a caveat"
  (the property the current `attenuate_narrows` does **not** give, `GROUND-AUTH §1.6`).

### 6.4 Effects-as-comodel-of-a-theory: a USER-EXTENSIBLE effect ISA
- **Fit:** if the core is *the algebraic theory* `T`, then a verified app can **extend `T`** with new
  operations + equations and ship a *comodel-homomorphism proof* that its extension refines the core. This
  is the principled version of `Effect::Custom` / `CellProgram::Cases` — instead of a `Bool` escape hatch,
  a new effect is a theory extension with a proof obligation.
- **New vs rephrase:** **new** — today `Custom` is an untrusted predicate (`GROUND-STORAGE §5` warns
  "moved-complexity unless the DSL is itself verified"). A theory-extension-with-refinement-proof is the
  *verified* version of userspace effects.
- **Build:** the hard part; needs the `CellProgram` law proved first (`REORIENT §5`), then an extension
  calculus. This is the genuinely-research-grade item.

### 6.5 The unified await/return as the second leg of the lens (zkRPC, native)
- **Fit:** `returnProject` is the *get* of a backward lens; `awaitSettle` is the caller's resumption gate.
  Forward turn + return projection = a **bidirectional lens** = an agent calling a tool and getting a
  proof-carrying result (`cand-A §2.2`, `EFFECT-ISA §3` #4).
- **New vs rephrase:** **new as a typed effect** (today `PipelinedSend` is a near-noop, `EFFECT-ISA §S10`).
- **Build:** one-shot (linear) continuation typing so conservation falls out (`cand-A §3`); the settled-call
  await face (`GLOSSARY: await family`).

### 6.6 Checkpoint/fork/time-travel as theorems + `forkSpan` as the *only* new structural primitive
- **Fit:** the codata + retained log give checkpoint/restore/replay as *consequences* (`cand-A §5`);
  `forkSpan` (a span/pushout, **not** a coproduct, `cand-A §6`) is the one primitive time-travel needs.
- **New vs rephrase:** **mostly theorems** (rephrase of codata); `forkSpan` is a **new** primitive.
- **Build:** the living cell must land first (`REORIENT §5`); then fork is the span with hand-proved
  attenuation+conservation merge laws (`cand-A §6`).

### 6.7 The recursion/accumulation backend as a swappable modality (defer perf, keep soundness)
- **Fit:** aggregation of step-proofs into a forest (`circuit/src/proof_forest.rs`) is **not an effect** —
  it is the JointTurn/finality layer above the ISA (`EFFECT-ISA §3`). The folding-scheme literature
  (`pdfs/`: nova/protostar/hypernova/latticefold/halo-infinite-accumulation) is *exactly* the swappable
  `RecursionBackend` (`GLOSSARY: RecursionBackend`, never an `additive_combine` method).
- **New vs rephrase:** **rephrase** — the architecture already says recursion is deferrable and behind a
  trait. dregg4's contribution is to make the trait a **modality on the attestation** (succinct-history
  badge vs leaf badge) rather than a circuit detail.
- **Build:** keep FRI/BabyBear leaf; the PQ recursion swap (latticefold target) is the deferred perf item.

### 6.8 Accountable anonymity: the de-jure/de-facto split as a FOURTH face? (surprising)
- **Fit:** `cand-C §0`/`GLOSSARY: the badge` insist permission (de-jure) ≠ authority (de-facto); the badge
  attests permission, the *log* carries authority. The anonymous-credential literature on **accountable
  anonymity + auditable revocation** (`pdfs/towards-accountability-for-anonymous-credentials`,
  `publicly-auditable-privacy-revocation-anoncreds`) suggests a *fourth projection*: an **escrowed
  de-anonymization capability** — anonymity that an authorized auditor can lift under a turn (itself
  attested). This is the "anonymous-collaboration-OS that still has accountability" story.
- **New vs rephrase:** **new** — neither the candidates nor the grounding propose accountable-anonymity as a
  modeled face. It fits as a *second transferability-like dial on the anonymity*: who (if anyone) can
  later open the pseudonym, gated by a capability.
- **Build:** an escrow-key + a non-membership/opening circuit; the revocation non-membership seam
  (`cand-C §6`, `pdfs/private-delegation-nonmembership-proof-updates-accumulators`) is the same machinery.

### 6.9 Storage durability as an honest below-the-ISA portal (kill the `rfl` fiction)
- **Fit:** WAL/redb crash-safety is **not** a face — it is infrastructure below the turn (`GROUND-STORAGE §4`).
  dregg4 models it as a **crash/recovery portal** with a `replay = pre-crash-state` theorem, *not* as the
  `CellRuntime` `restore∘checkpoint = rfl` label-fiction (`GROUND-STORAGE §3` "sharpest fiction risk").
- **New vs rephrase:** **new (honesty)** — replaces a vacuous theorem with a real crash model.
- **Build:** a log + fault-point + replay-equals-pre-crash theorem (`GROUND-STORAGE §4` #2).

### 6.10 Choreography as the modal front-end (the syntactic spine, `cand-D`)
- **Fit:** a global type `G` is a *diagram in the turn-category*; projection is a *functor to comodels*; the
  monitor *is* the vat-boundary verifier; blame *is* the de-jure/de-facto split (`cand-D §2`). The three
  judgements become one annotated `G` (`cand-D §1`).
- **New vs rephrase:** **rephrase + deferred** — `cand-D` already designs this; dregg4 just notes it is "the
  modal front-end whose back-end is the unified turn," built last (`cand-D §8`).
- **Build:** last; rests on open theorems (Byzantine-EPP-by-monitoring, `cand-D §7`).

---

## 7. What dregg4 *means* as a clean rebuild, given everything learned this session

Four findings reshape the rebuild target:

1. **De-vacuification** (the swarm caught ~4 false-as-stated theorems; `REORIENT §6`, tasks #107–#114): the
   rebuild must state the three faces as *non-vacuous* conjuncts of one `StepInv` — the comodel framing
   (§5.2) makes vacuity *structurally* hard, because a face that did nothing would fail bisimulation.
2. **Fidelity grounding** (`GROUND-AUTH`/`GROUND-STORAGE`): "carry the Rust semantics, not a Lean fiction."
   dregg4's caveat face must carry the *real* HMAC chain / 3P crypto / selective disclosure, and its storage
   face must carry the *real* WAL — both as explicit §8 portals, never as `Bool`/`rfl`.
3. **The ISA reshape** (`EFFECT-ISA`): the effect face is ~11 shapes, not 54 names; the rebuild starts from
   the small core + the named-new primitives (per-asset, half-edge, ρ_in/ρ_out, return, fork).
4. **The repudiation gap** (`GROUND-AUTH §2`): the attestation face is a *single point* of a lattice it
   should range over. dregg4 *is* the system where attestation is modal.

So **dregg4 = one guarded comodel of a small effect theory, emitting a modal attestation, with caveats as
the theory's guards and the two-(three-)dial lattice as the attestation's modality** — and storage,
credentials, deniable interaction, cross-chain, and choreography are all *instances*, not subsystems. dregg2
(the current target, `CARRY-FORWARD-SYNTHESIS §4`) is the faithful three-face kernel; dregg4 is its
*generalization to the full modal lattice with a user-extensible theory*.

---

## 8. Honest bounds (design around these; do not "fix")

- **The public badge cannot be dropped from the forest path** (`GROUND-AUTH §2.3`): transferability is
  load-bearing for finality. The deniable/designated modes are *companions*, never replacements there.
- **`νF₁ ⊗ νF₂` is not final** (`study-category`, `GLOSSARY: JointTurn`): the comodel tensor's cross-cell
  soundness is an *irreducible hypothesis* (CG-2⊗CG-5), not derivable from per-cell soundness. The lens
  framing makes composition free *for sequential* composition; the *parallel* (JointTurn) tensor still
  carries the binding as a premise.
- **No unconditional IVC** (`cand-A §2.4`): depth = security parameter; the accumulation modality (§6.7) is
  bounded.
- **User-extensible effects (§6.4) need the `CellProgram` law proved first** — until then, theory-extension
  is moved-complexity (`GROUND-STORAGE §5`). It is the research-grade item, correctly last.
- **Revocation has a recency floor under partition** (`cand-C §7`): the agreement dial cannot give instant
  global revocation local-first; prefer short-expiry+renewal.

---

## 9. Ranked shortlist

### Most PROMISING (highest value, clearest fit, buildable)
1. **The modal attestation `Obs[t]` + verifier-indexed `Discharged[V]`** (§4.2, §6.1). Closes the only
   structural privacy hole in an anonymous-collaboration OS; orthogonal to the other two faces; the
   verifier-indexing is the one *named-new* piece of theory the session surfaced. **Build:** DVZK companion
   + Lean `Discharged[V]`. *This is the single most important dregg4 idea.*
2. **The caveat-chain algebra unifying the token zoo** (§3.1, §6.3) with **real HMAC-tail integrity**
   modeled (the current unflagged §8 fiction). High fidelity-debt payoff; mostly collapse + one new law.
3. **The small-core ISA + per-asset conservation + ρ_in/ρ_out + half-edge** (§3, `EFFECT-ISA §5`). The
   effect face done right; per-asset conservation is the #1 soundness gap.
4. **Storage durability as an honest crash-recovery portal** (§6.9) — kills the `rfl` label-fiction; pure
   honesty gain.
5. **`returnProject`/`awaitSettle` (native zkRPC)** (§6.5) — the bidirectional lens; the agent product.

### Most SURPRISING (galaxy-brain; not previously considered)
1. **The third dial — Agreement/finality on the same footing as disclosure & transferability** (§4.3): the
   attestation is a point in a `Disclosure × Transferability × Agreement` 3-cube, and the system lives on
   one edge. *Not in any candidate or grounding doc.*
2. **The turn as a guarded comodel of an effect theory; the three faces as the lens's get/put/guard** (§5):
   one object, one soundness theorem, free sequential composition, dials-as-modalities. Dissolves the
   "two co-primary primitives" tension structurally.
3. **User-extensible effect ISA via theory-extension-with-refinement-proof** (§6.4): the *verified* version
   of `Custom`/userspace effects — a comodel homomorphism, not a `Bool` escape hatch.
4. **Accountable anonymity as a fourth face** (§6.8): an escrowed, capability-gated de-anonymization — the
   "anonymous yet accountable" story for a collaboration OS, reusing the revocation non-membership seam.
5. **`capExercise` = lens composition** (§5.1): the recursive inner-effect gating the circuit must bake is
   *not* a special case — it is the compositional structure of the lens, which reframes the hardest CORE
   selector as the most natural one.

---

*A closing couplet, since the egg is dreaming bigger now:*
*one turn, three faces — what it does, may, and shows; / and two (then three) dials for how far each one goes.*
*the token, the queue, the proof that can't be relayed — / are one guarded comodel, in a modal lattice arrayed.* 🐉🥚
