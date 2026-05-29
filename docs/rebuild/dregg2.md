# dregg2 — The Canonical Architecture

> **Status:** THE consolidated dregg2 architecture. This document **supersedes and
> indexes** the three candidate explorations (`cand-A-vat-coalgebra.md`,
> `cand-B-witness-pca.md`, `cand-C-cap-distributed.md`), reads forward from
> `00-synthesis.md` + the three spine docs (`01`/`02`/`03`) + `pdfs/discoveries.md` +
> `pdfs/decisions.md`, and pins the metatheory module map (`metatheory/README.md`,
> `metatheory/Metatheory/Authority/Positional.lean`).
>
> **The decision, made:** *none of the three candidates rivals the others — they are
> three projections of one object at OS-scale.* dregg2 **composes** them:
> **C = the authority SPINE ⊕ B = the trust LAW ⊕ A = the soundness STYLE & runtime
> CHARACTER (coinductive).** This is not a compromise; it is the recognition that the
> spine explorations *already* found one generator with three faithful projections
> (`00-synthesis §1`), and the candidates are those projections driven to OS-scale.
>
> **Tags:** `[G]` grounded-in-paper · `[C]` grounded-in-code (`file:line`) · `[F]`
> forward-design. Untagged prose is connective tissue.
>
> **Core correction (this revision):** five things the gap analyses (`gaps-1`,
> `gaps-2`) mis-filed as "strata above the core" are in fact **core**, and are now
> first-class: the cell's structure-map (`CellProgram`, §1.5), the cross-cell tensor
> `⊗` (§1.6), cell-liveness/GC (§1.7), the three-tier privacy stack (§6a), and the
> multiagent/zkRPC product surface (§6b). Only an operational shell — node daemon,
> gossip transport, relay/fee economics, on-chain settlement — remains genuinely above
> the core (§10).

---

## 0. Vision — Robigalia

dregg2 is **seL4's capability discipline extended across an untrusted global
network**: a *persistent distributed operating system* where developers collaborate
on untrusted code without getting hacked, and where **checkpoint / restore / replay /
time-travel / advanced debugging are native consequences of the design, not
bolt-ons**. `[F]`

The literal question (cand-C §0): seL4 proves a machine-checked **integrity
theorem** — a subject modifies only what its caps authorize — resting on *one trusted
kernel* mediating every invocation. dregg2 deletes the single kernel and spreads the
same authority structure across mutually-distrustful hosts, content-addressing, and
proofs. The honest answer up front: **permission survives the crossing; authority
does not** (Miller `BA`-vs-`TP`, `discoveries §3.6`). The cross-net structure can
prove *a legal derivation path existed* (de-jure); it cannot prove what a holder can
eventually *cause* (de-facto, recovered behaviorally from the log). That split is not
a defect — it is the load-bearing discovery, and the reason "seL4 across the net" is
honest rather than a slogan. `[G]`

---

## 1. The composition — three projections of one generator at OS-scale

The turn (morphism) is the generator. It has three faithful projections — none total
— under two ambient laws no projection owns (`00-synthesis §1`). dregg2 assigns each
candidate to the projection it drove hardest, and **composes** them: `[F]`

### 1.1 C = the authority SPINE — the CDT extended across the net `[G/C]`

The primary structural object is the **capability-derivation-tree, content-addressed
and gossiped across hosts** (cand-C §1). One identity holds it together:

> **CDT ≡ strand log ≡ biscuit delegation graph.** A capability *is* a derivation
> node; appending a turn *is* minting/exercising an edge; a biscuit's signed
> attenuation-chain *is* a path of monotone-narrowing `(parent → child)` edges from a
> `RootSeal`. One append-only content-addressed partial order, three renderings
> (kernel RAM / blocklace / offline credential). `[F]`

The seL4 carry-across (cand-C §1, the four kernel-object analogs):

| seL4 | dregg2 | role |
|---|---|---|
| CNode / kernel object | **cell** | endpoint + c-list cache of held `CapHash`es (the CNode-analog) |
| invocation (`Call`/`Send`) | **turn** | the morphism; a bundle of cap *exercises*; **the rollback handler** |
| `Mint` with reduced rights | **attenuation edge** | the *one* rule the system rests on |
| CSpace / kernel↔thread | **vat / trust-root boundary** | the kernel↔network seam (host = trust-root) |
| the kernel (single, trusted) | **(consensus + content-addressing + proofs)** | the de-centered mediator |

The l4v integrity theorem — the `troa_lrefl`-vs-policy-edge case-split (own-it ⟹
arbitrary change / non-owner ⟹ authorized policy edge) — **is the vat-boundary law**
(`Positional.lean`). `[G]`

### 1.2 B = the trust LAW — soundness-by-verification `[G]`

The TCB is **the verifier**: a proof-checker + signature/hash axioms + one decision
procedure `Verify P w : Bool` (cand-B §1). *Everything else* — delegation, policy,
conservation, ordering-search, intent-matching, schema-migration, handler-selection —
is defined inside **checkable witnesses produced by untrusted solvers**.

> **The organizing law (one seam, four independent derivations — `discoveries §1`):**
> every *gate* is cheap to **VERIFY**; every *search* is intractable to **FIND** and
> must be an untrusted, witness-emitting plugin. **Soundness is by verification, never
> by construction; the TCB is the verifier, never the solver.** `[G]`

This is sharper and more defensible than "proof is truth" (which over-claims
canonicity — `03 §10`). It is applied *uniformly*: auth-path search, intent-match,
ordering, schema-migration, and handler-selection are each a `…Plugin` the same tiny
TCB checks. The step-complete PCA turn-proof (§7) is its primary object.

### 1.3 A = the soundness STYLE + runtime CHARACTER — coinductive `[G/T]`

A cell is **live CODATA** — an element of the final coalgebra `νF`, `F X = Obs ×
(AdmissibleTurn ⇒ X)` (cand-A §1, `decisions §2`). The keystone type:

```
Cell = νC. µI. StepProof I × (Turn ⇒ C)
```

outer `νC` = the unbounded life of the cell (never bottoms out); inner `µI` = the
*bounded* per-turn proof obligation tree (the depth-1 bounded-fan-in aggregation);
the guard is Birkedal's `▶` ("later"), typed off `previous_receipt_hash`. `[G/T]`

This is the *style* in which soundness is stated (a ▶-guarded bisimulation) **and**
the *character* of the runtime: checkpoint/restore/replay/time-travel/debugger are
**theorems**, the definitional consequences of (codata + retained log + rollback-
handler turn), with zero new machinery (§ runtime, below). `[F]`

### 1.4 Why composition, not a winner

Each spine doc, pushed hard, *shed* the same two things it could not own —
conservation and ordering (`00-synthesis §1`); each candidate doc *refused* the
totalizing slogan its own lens tempted ("everything is a cap / proof is truth /
everything is a cell"). The three are not rivals because **C answers *what the
structure is*, B answers *what the trust rests on*, A answers *what soundness means
and what the runtime feels like*.** They sit under the two ambient laws of §2.

The next three subsections (§§1.5–1.7) make first-class three pieces of the **core**
that earlier gap analyses mis-filed as strata above it: the cell's structure-map
(`CellProgram`), the cross-cell tensor (`⊗`), and cell-liveness (GC).

### 1.5 CellProgram = the coalgebra structure-map (the center) `[C/F]`

The keystone type above writes `(Turn ⇒ C)` as if the admissibility arrow were
ambient. It is **not** — it is *carried by the cell itself*, and the thing that
carries it is the **`CellProgram`** (`cell/src/program.rs:53`). This is the center of
the cell model, currently buried one level down. State it plainly:

> **A cell = (identity, `Preserves` state, `CellProgram`); the `CellProgram` IS the
> `AdmissibleTurn ⇒ Cell` arrow of `step : Cell → Obs × (AdmissibleTurn ⇒ Cell)`.**

`step` factors into two jobs the `CellProgram` performs together:

1. **The admissibility filter** — *which* turns are admissible, and *to which*
   post-state. This is the dependent shape of the arrow: `AdmissibleTurn` is not a
   fixed set, it is `{ t : Turn | program.evaluate(old, new(t), ctx) = Ok }`. The
   program **decides the domain of the arrow.**
2. **The effect-semantics** — *what the post-state is*, i.e. the codomain selection
   inside `Obs × (…)`.

The caveat/predicate/StateConstraint system is exactly the **`WitnessedCondition`s
that *compose* this arrow** (the universal gate of `00-synthesis §3.1`). dregg's
`CellProgram = None | Predicate(Vec<StateConstraint>) | Cases(Vec<TransitionCase>) |
Circuit { circuit_hash }` (`program.rs:53-97`) and the **~29-variant `StateConstraint`
catalog** (`program.rs:597-829`: `FieldEquals`/`Gte`/`Lte`/`SumEquals`, `Immutable`/
`WriteOnce`/`Monotonic`/`StrictMonotonic`, `FieldDelta`/`FieldDeltaInRange`,
`FieldGteHeight`/`FieldLteHeight`, `BoundedBy`, `SumEqualsAcross`, `SenderAuthorized`/
`Renounced`/`CapabilityUniqueness`, `RateLimit`/`RateLimitBySum`/`TemporalGate`,
`PreimageGate`, `MonotonicSequence`, `AllowedTransitions`, `TemporalPredicate`/
`Witnessed`, `BoundDelta`, `AnyOf`, `Custom`) **map onto compositions of
`WitnessedCondition`s**, exactly as `00-synthesis §3.1` predicted:

| `CellProgram` shape | structure-map reading |
|---|---|
| `None` | the *terminal* program: every authorized turn admissible (`step` = identity-filter) |
| `Predicate([c…])` | the arrow's domain = `⋀ cᵢ` — a conjunction of gates (the legacy `Always`-case) |
| `Cases([{guard, [c…]}…])` | a **method-dispatched** arrow: the guard selects which gate-conjunction binds (`MethodIs`/`EffectKindIs`/`SlotChanged`); **no matching case = default-deny** (`program.rs:1106`) — the arrow is *partial* and the undefined region is empty, not permissive |
| `Circuit { circuit_hash }` | the arrow is given *opaquely* by an AIR; admissibility = "the turn carries a proof the circuit accepts" |

The Heyting fragment (`AnyOf` ⊔, `SimpleStateConstraint::Not`, derived `implies`,
`program.rs:463-563`) makes the gate-algebra a genuine Heyting algebra — the
`Predicate ⊣ Witness` adjunction of `00-synthesis §1` realized in the slot-caveat
vocabulary. **The program is content-addressed**: `AIR-id = H(canonical(schema_decl))`
(`§5`), `Custom { ir_hash, … }` keys the DSL IR by hash, `Circuit { circuit_hash }` *is*
its hash. So a `CellProgram` value **is** a schema/AIR identity — the structure-map is
itself a content-addressed object the CDT can name. This is the heart of the cell
model: everything else (conservation, authority, await) is a *clause* the structure-map
must attest on the arrow it defines (§7.1's `StepInv`).

### 1.6 Cross-cell aggregation = the monoidal ⊗ (core correction) `[C/F]`

The symmetric-monoidal Core (§2.1) was *chosen* precisely so a turn can range over
**more than one cell** — but the keystone type as written models only the single-cell
arrow, and `gaps-1 §(b)/§(d)` correctly flag that cross-*cell* binding is missing from
it. The correction, made core:

> **A turn over N cells = a morphism on the tensor `C₁ ⊗ … ⊗ Cₙ`.** The per-cell
> coalgebras compose via `⊗` (the monoidal product the Core already carries); the
> **cross-cell binding** — *all cells agree on the one shared turn* — is the
> **equalizer / pullback** of the N per-cell `step` maps over the shared turn-identity.

Extend the keystone so a `Turn` ranges over a tuple of cells:

```
Turn ⊗ : (C₁ ⊗ … ⊗ Cₙ) → Obs⊗ × (AdmissibleTurn ⇒ C₁ ⊗ … ⊗ Cₙ)
```

This is **already built** as γ.2: the per-cell halves are declared by
`StateConstraint::BoundDelta { local_slot, peer_cell, peer_slot, delta_relation }`
(`program.rs:747`, the `EqualAndOpposite` paired swap = the bilateral conservation
identity); the aggregate proof is `circuit::bilateral_aggregation_air`
(`CrossSideExistenceAir`, the signed edge-fingerprint balance sum == 0,
`bilateral_aggregation_air.rs:805`) driven by `turn::aggregate_bilateral_prover`. The
AIR's constraint groups *are* the equalizer conditions: **CG-2 turn-identity
agreement** (every cell's row agrees on `TURN_HASH`/`EFFECTS_HASH`/`ACTOR_NONCE`/
`PREVIOUS_RECEIPT_HASH` — this is the pullback over the shared turn) + **CG-5
cross-side existence** (every claimed half-edge has its matching peer half — the
balance is the equalizer). **Soundness of a cross-cell turn = per-cell
step-completeness (§7.1) ∧ the cross-cell agreement binding** (CG-2 ⊗ CG-5). The
`ring_closure` coequalizer of N transfers is the cyclic (CoW-ring) case of the same
construction. This makes "atomic cross-cell turn" — flagged unbuilt in `00-synthesis
§6.3` — cohere: it is the `⊗`-morphism, proven by γ.2.

> **Crucial: `νF₁ ⊗ νF₂` is NOT a final coalgebra** (`study-category`). The tensor of
> two final coalgebras is not itself final, so **cross-cell soundness is irreducible to
> per-cell soundness** — the CG-2 ⊗ CG-5 binding is an **explicit HYPOTHESIS, never a
> theorem derivable from `per-cell-sound ∧ per-cell-sound`** (deriving it would make the
> Boundary module unsound). CG-5 is the *price of having no global ledger*; Mina never
> needs it because one ledger gives one namespace. This is the seam flagged in §10's
> honesty note — the one place the single-cell coinductive frame is *extended*, not
> *inhabited*.

### 1.7 CapTP GC = cell-liveness, the dual of coinductive existence `[C/F]`

`gaps-2 §(a)` flags distributed GC as "genuinely absent," and notes the coinductive
"never bottoms out" framing (§1.3) *actively obscures* it. This is a real tension and
the resolution is core, not above it: **codata unfolds forever (`ν`) UNLESS it becomes
unreachable.** Liveness is not unconditional — it is conditional on reachability. So
the keystone gets a side-condition dual to its productivity guard:

> **A cell whose inbound capability-edges are all dropped is collected** — it
> transitions to a **terminal lifecycle state** (`CellLifecycle::Destroyed`/`Archived`,
> the terminal objects of `00-synthesis §5.1`). GC = reachability-pruning on the CDT.

This **folds into CDT-reachability** (§1.1): a `CapabilityRef` (`cell/src/capability.rs:43`,
the c-list entry pointing at a `target` cell) is an inbound edge; a cell is *live* iff a
root-reachable path of un-dropped `CapabilityRef`s reaches it. The `ν` says "while
reachable, the unfold never bottoms out"; reachability *is* the codata's
well-foundedness side-condition.

**Distinguish two graphs — `refcount==0` is NOT, in general, "unreachable."** The
**CDT/derivation graph is acyclic** (the append-only, monotone-attenuation partial
order of §1.1) — there, a node with no inbound un-dropped edge truly is unreachable, and
refcount-at-zero collects it soundly. But the **live capability/reachability graph can
be cyclic** (cell A holds a ref to B, B holds a ref back to A), and on a cyclic graph
**plain refcounting does not detect unreachability**: a dead cycle keeps every member's
refcount ≥ 1 forever. So GC is two distinct mechanisms: (1) **acyclic CDT pruning** =
refcount drop-to-zero (`captp/src/gc.rs`: `ExportGcManager`/`ImportGcManager`,
per-holder `RefCount`, session-validated `DropRef`, `DropResult::CanRevoke` at zero) —
the cheap, local, already-built half; and (2) **cyclic-liveness collection** = a
reachability trace from roots (mark-from-roots / cycle detection) that refcounting
*cannot* substitute for. The `ν` "while reachable" qualifier is the latter; the runtime
implements only the former today, and the cyclic case is genuinely open (see closing
honesty note).

**Distributed GC = the await/discharge family (§4), not new machinery.** The cross-vat
drop is itself a discharge: the importing vat's "drop far-ref" (`ImportGcManager` →
`DropRef`) is a *resolution* the exporter awaits, which discharges (decrements) the
exporter's `RefCount`; at zero the export edge is collected. So GC's drop-protocol is
the **backward face** of the same await engine that powers discharge — a `DropRef` is a
settled negative-acknowledgement that advances the exporter's `Obs`. The code's
`TODO(unified-lace)` (key GC on `StrandId`, not `FederationId` — `gc.rs:14`) is exactly
the bilateral-strand framing this section makes core. The coinductive type **absorbs
GC cleanly** as a reachability side-condition; it does *not* strain (see closing
honesty note).

---

## 2. The judgements (the ribs no projection owns)

> **Three orthogonal judgements, not "two laws."** Conservation (Law 1, §2.1) and
> ordering/canonicity (Law 2, §2.2) are the two ambient laws every projection sheds;
> but a third, **independent** judgement — **I-confluence** (invariant-merge,
> §2.3) — is *not* derivable from either and is **NOT** the session type. A turn
> carries all three: conservation (linearity), ordering (session/canonicity), and
> I-confluence (does this write commute/merge invariant-safely under concurrency).
> "Two laws" is retained below only as the historical framing for the two *ambient
> category structures*; treat I-confluence as a co-equal third judgement
> (`dregg2-multicell-privacy.md §6`, `study-choreography`).

### 2.1 Conservation — Law 1 `[G]`

`Σ_k` is a **monoid-homomorphism `(Turns, ∘) → (ℕ, +)` plus an invariance condition**
— it sends a cell to its `k`-resource count and is **constant on every non-mint/burn
hom-set** (`discoveries §3.2`, `Core.lean`). *(The earlier "strong monoidal functor"
phrasing was decorative — the load-bearing content is the monoid-hom into `(ℕ,+,0)` +
invariance on ordinary turns; the `μ`/`ε` laxator coherence of a strong monoidal
functor is not what conservation rests on. `Core.lean`'s headline theorem is the
monoid-hom + `conservation_ordinary` invariance, with the functor packaging flagged
decorative.)* Conservation =
withholding the cartesian copy `Δ` and erase `◇` maps (Selinger / Girard); the system
is a **symmetric-monoidal category, thin only in its ordering fragment** — never a
"thin posetal" category (which cannot carry Law 1's symmetry iso). It is invariance
(`=`), stronger than a Coecke-Fritz monotone (`≥`); **mint/burn are explicit typed
generators**, the only homs permitted to move the count. Folded *per-asset* into the
proof (§7, the "second rib"), never one aggregate scalar. `[G]`

**Resource model — the camera is CANONICAL (decided 2026-05-29).** "Numbers summing"
is the *free/simplest* case, not the model. The conserved value lives in an arbitrary
`AddCommMonoid M` (`Core.lean`: `count : Cell → M`, one law `count B = count A + val
tag`), which already covers multi-asset (`M = K → ℕ`), fractional (`ℚ≥0`), and debt
(`ℤ`). But the resources that *matter for a cap OS* — NFTs/linear tokens, fractional
permissions, the sovereign-total↔holder-fragment split, and **capabilities themselves**
— have a **partial** composition (it can be *invalid*), which no monoid expresses. The
canonical structure is therefore Iris's **camera** (a partial commutative monoid +
`valid` + `core`; `Resource.lean`), and the canonical conservation law is the
**frame-preserving update** `a ↝ b ≜ ∀ f, valid(a·f) → valid(b·f)`; sum-conservation is
its `(ℕ,+), valid≡⊤` shadow. **The prize:** at this tier conservation and authority are
*one law* — `ConfinesAuthority := Fpu` (Iris shares ghost-state and permissions in one
algebra), unifying §2.1 with §3. *Proved in Lean (no `sorry`):* the `ℕ` camera, `Fpu`
refl/trans, NFT non-duplication (`excl_no_dup`). *Sketched:* the `Auth M` camera +
`conservation_is_fpu` (a fragment move is frame-preserving iff it enlarges no frame's
claim — withdrawal always, deposit only against headroom). **The camera is FULL, not
ZK-restricted** (correction): resources run in two registers mirroring caps↔keys — the
**runtime/intra-vat** register (caps-as-caps, mediator-enforced) admits *any* camera,
no circuit; only the **attested/cross-vat** register (keys-as-caps) needs `valid` to be
an in-circuit succinct `Verify`. The ZK-able cameras are a *sub-fragment* (what may
travel as a proof-carrying certificate), never a ceiling on the metatheory. The full
Iris **camera** (step-indexed OFE + extension axiom) is reached when resources go
higher-order/recursive — and then shares `Boundary.lean`'s `▶` guard (Iris's `iProp` =
guarded fixpoint over cameras); until then a discrete RA (with the three core laws) is
canonical. `[G]`

### 2.2 Ordering — Law 2: the pluggable finality tier `[G]`

Canonicity (which valid history is *the* history) is **not** in any proof — it is a
per-cell pluggable **finality tier** on top of one DAG (a join-semilattice CvRDT,
proven Merkle-CRDT; `discoveries §4`). `τ_unified(B, G, C)` runs τ per reference-
group; `C` selects the rule; the hardcoded `½(n+f)` lifts into group config. `[G/C]`

| Tier | mechanism | n | synchrony | partition |
|---|---|---|---|---|
| **1. Causal-only / CRDT** | add block; causal order | 1+ | none | **never blocks** (phones over BLE keep working) |
| **2. Ack-threshold** | k-of-m acks, no leader | small | none for safety | degrades to tier 1 |
| **3. Cordial-Miners τ-BFT** | waves + leader + 3-step ratify | known Π, n≥3 | GST/async | **stalls**, resumes after GST |
| **4. Constitutional** | τ-BFT + self-amending `(P,σ,Δ)` | known P, PKI | partial-sync | stalls + deadline |

**The I-confluence well-formedness side-condition (`discoveries §3.7`):** a cell may
select tier-1 **only if** its state is a bounded join-semilattice with
invariant-preserving joins (`I(x) ∧ I(y) ⇒ I(x ⊔ y)`); else it is a **static type
error**. Hash-keyed nullifier uniqueness qualifies; `balance≥0` does not (needs
≥tier-2 or single-owner). Cross-tier rule: a turn commits at the **join** of its
written cells' tiers; effects held until the join-tier commits; no finalized value
downgrades; conservation is tier-independent and only prunes the order search.
Adopt constitutional **amendment rules** as the tier-4 plugin; **reject** its four
globalism seams (single global total order; GST-as-precondition-for-any-progress;
fixed σ-quorum forbidding n=1; synchronized wall-clock deadline). `[G]`

### 2.3 I-confluence — the third, orthogonal judgement `[G]`

I-confluence is **not** a corollary of conservation or ordering, and it is **NOT the
session type** (the classifier of §2.2's tier eligibility is a *separate analysis*).
It is a **BEC invariant-confluence judgement over the turn's `write-set ×
cell-state-lattice`**: do concurrent writes merge invariant-safely (`I(x) ∧ I(y) ⇒
I(x ⊔ y)`)? The two axes are genuinely independent: **linear ⇏ I-confluent** (two pool
withdrawals are each linear yet jointly overspend), and **I-confluent ⇏ linear** (a
monotone counter merges freely but is not conserved). CryptoConcurrency shows
I-confluence *reduces from consensus*, so it is a distributed-agreement obligation, not
a typing one. It is what gates §2.2's tier-1 eligibility and §6b/multicell's
cross-group fast path; carry it per-turn alongside conservation (linear) and ordering
(session). `[G]`

---

## 3. The keys-as-caps token layer

Inside a vat, authority is **caps-as-caps** (positional CSpace slots, kernel-
mediated). On exit it becomes **keys-as-caps** (epistemic, crypto-unforgeable, freely
copyable). The concrete carriers are `Authorization::Token { encoded, key_ref,
discharges }` + `TokenKeyRef` (`turn/src/action.rs:422`). `[C]`

- **biscuit** (`eb2_…`, `TokenKeyRef::BiscuitIssuer`) = **cross-vat**: public-key
  (Ed25519) verifiable offline by *anyone* (UCAN-class, DID-rooted attenuation-chain).
  This is what an `Obs` badge wears when it leaves the vat. The biscuit delegation
  graph **≡** the distributed CDT (§1.1). `[C/G]`
- **macaroon** (`em2_…`, `TokenKeyRef::CellScopedMacaroon`) = **intra-vat**: cell-
  scoped HMAC — near-reference convenience inside one trust-root, never cross-domain
  (HMAC ≠ third-party-verifiable, `discoveries §6.3`). `[C/G]`

**The `ρ_in`/`ρ_out` lossy attenuation-only caps↔keys conversion at the vat
boundary.** `ρ_out` serializes a held slot into a biscuit key-as-cap; `ρ_in` re-mints.
Both are the forgetful functor Φ dropping *exactly* Miller's Property F (confinement)
+ Property E (revocable forwarders) — a **named, exact loss** (`discoveries §2b`,
`Positional.lean::lossy_attenuation_only`). A key may only narrow. The token layer
*is* the operational realization of the LossyMorphism theorem. `[G]`

**Discharge = the await engine's authority-face.** A 3rd-party caveat
`cav@Loc⟨cId,vId⟩` is a turn that cannot become admissible until another vat resolves
it: the **gateway** = the named resolver, the **discharge token** (`discharges`) = the
resolution, `bindForRequest = H(M'.sig :: M.sig)` = the binding-site (isomorphic to
`ConditionalTurn`). `[C/G]`

**Revocation = the lone consensus seam.** A **negative discharge** — a STARK
*non-membership* proof against an attested revocation root — the de-facto dual of the
path-proof (path says "permitted"; non-membership says "not since revoked"). The only
op needing globalism, and only **root-epoch agreement**; everything else stays local +
offline. Prefer short expiry + renewal over revocation; any design claiming clean
global revocation under local-first is lying. `[G]`

---

## 4. Await = gate-engine + linear continuation-capture

Continuations are the *one* effect that is **NOT** algebraic (Plotkin-Power,
`discoveries §3.5`) — so the turn is **not** "the free model of await." The await
substrate is **two layers**: a gate-engine (algebraic handler / `Verify`) + a
delimited continuation-capture primitive. **The turn IS the rollback handler**: it
holds its outgoing effects until commit; commit = replay-the-held-list + advance the
`▶` step + (at a vat boundary) emit the witness; abort = discard =
conservation-preserving refund. The deferred-prover keystone is exactly "the
commit-replay handler emits the witness lazily, at the crossing." `[G]`

**One-shot is STATIC conservation typing on the zkpromise, not a runtime check** —
linear (one-shot) continuation typing makes conservation fall out as a corollary
(Dolan's "raise on 2nd continue" becomes *derivable*); multi-shot is sound only for
`Copy`/non-conserved payloads. `[G]`

**One `Await`/`Resolver` inductive** (`named | gateway | ∃P | registry`); matching =
a **bounded oracle-solver over a decidable fragment + WDP**. The four faces:

| Face | Resolver | Direction |
|---|---|---|
| zkpromise / zkawait | specified party | forward, point-to-point |
| discharge (3rd-party caveat) | named gateway | forward, the `Await` *engine* of the universal gate |
| intent | *any* filler satisfying P (∃) | the **inverse** vat boundary: gates the *missing half* |
| **settled-call return** | the callee's advanced `Obs` | **backward** — the return projection (§6) |

The **VERIFY/FIND seam is sharpest here**: VERIFY a claimed fill = tractable; FIND a
fill = undecidable (`no_general_matcher` via `HOU ⪯ GeneralMatch`). The matcher is a
bounded, pluggable, untrusted plugin emitting a checkable witness; soundness-only
contract (completeness/termination explicitly NOT required); Winner-Determination is
NP-hard with no PTAS. `[G]`

---

## 5. Data substrate (Preserves)

One idea closes both `EffectMask` bit-fragility AND the frozen-AIR trap: **identity =
hash of a canonical data-model value** (`discoveries §5`). `[G/F]`

- **cell-state** = name-keyed `Record @schema #"air-id"`.
- **facet** = canonical **Set of effect Symbols** (adding `transfer` adds an
  *element*, never shifts a bit position — kills `EffectMask` fragility).
- **AIR-id** = `H(canonical(schema_decl))` (kills the frozen/unversioned AIR — the
  Urbit trap).
- **caps** = Embedded (the caps↔keys conversion point).
- **typed schema-upgrade** = lazy `migrate-on-read`, sound iff **transparent**
  (commitment-equality: lazily-migrated ≡ fresh-at-v2) **AND conservative** (a DROP
  over a linear slot emits `Σ before = Σ after + Σ dropped`). Forbid Preserves
  `Double`s; pin Embedded canonicalization before hashing. Transparency theorem is
  linear-chain only (schema-DAG / fork-merge migration is open). `[G]`

---

## 6. The two validated gaps, now folded in

1. **Per-asset value-conservation folded INTO the proof — the "second rib."** Not a
   side-check: a per-`LinearityClass` `CONSERVATION_VECTOR` sum-check chip on the same
   effect-stream rows the effect-fold absorbs (Pedersen sum-to-zero + range + asset-
   type + fee-as-asset), sharing the in-proof bus. This makes a badge a *value*-bearing
   artifact, not just a state-transition attestation. `[F]`
2. **The turn is one-directional → add a return projection.** A forward turn is the
   structure-map step `c : X → F X`; the **return** is a *second observation* the
   caller awaits. Add (a) a **result in the proof PI** (a typed `Obs`-delta the callee
   commits) + (b) a **"settled-call" await face** (request → response + detached
   proof; the caller suspends on "the callee's `Obs` advanced past receipt R"). zkRPC
   = a turn whose return projection is a proof-carrying `Obs`; this is the agent/zkRPC
   product. `[F]`

**Runtime character (the A-projection payoff, free from the above):** checkpoint =
name a point in the unfold (`(head, receipt)`); restore = re-seed the anamorphism;
replay = re-run from the log (DB is cache, log is truth); time-travel = fork the unfold
at a checkpoint (`Fork`); debugger = step the coalgebra under operator control (the
rollback handler exposed; breakpoints are admissibility predicates; a failed proof
shows *which `StepInv` conjunct* rejected). `[F]`

---

## 6a. Privacy = three tiers, on existing primitives `[C/F]`

`gaps-1 §(d)` calls dregg2's privacy "a strict subset." It is not — the full
cryptosystem already deployed composes into **three first-class tiers**, each built on
primitives that exist, distinguished by *what* is hidden:

1. **Field privacy** — *hide a field's value from the schema-public view.*
   `FieldVisibility` on `Preserves` fields (kept as an attested endpoint property,
   `00-synthesis §5.1`). The cheapest tier: selective disclosure of named slots.
2. **Value privacy** — *hide an amount while proving it conserves.* The **value rib**
   (§6.1): Pedersen commitments (`cell/value_commitment.rs`, Ristretto) + Bulletproof
   range, folded into the per-class `CONSERVATION_VECTOR` sum-check. The committed
   amount is hidden; sum-to-zero + range are proven in-circuit.
3. **Graph privacy** — *hide who-interacts-with-whom.* Two composing mechanisms: the
   **ZK-hidden auth-derivation-chain** (the CDT path is proven legal without revealing
   the nodes — anonymous delegation) + **holder-blinded set-membership**
   (`AuthorizedSet::BlindedSet`/`CredentialSet`, `program.rs:316/338`; the cell knows
   only a Poseidon2 commitment, the witness carries non-membership/non-revocation).

Three privacy primitives the gap analysis lists as "MISSING" are in fact the *carriers*
of tier 3, and become first-class here:

- **Blinded queue = a set-cell with ZK-blinded membership/consumption.** A queue whose
  elements are `Com(item) = Poseidon2(item, r)` and whose consumption publishes a
  **nullifier non-membership** proof + **holder-blinding** so the operator sees
  commitments-in / nullifiers-out but cannot link them (`storage/src/blinded.rs`;
  canonical home = the `dregg_storage_templates::blinded_queue` cell-program with a
  `Witnessed { Custom { BLINDED_QUEUE_SPEND_AIR } }` constraint — the **"sets → cells"**
  move of `00-synthesis §5.2` applied to the private queue). This is the missing
  inbox/mailbox primitive `gaps-1 §(c)` flags, recovered as a cell.
- **Unlinkable invocation = stealth one-time keys.** `cell/src/stealth.rs` (EIP-5564/
  Monero-style: ephemeral `r`, DH shared secret over the view key, one-time
  `P = H(r·V)·G + S`). A fresh, unlinkable `CellId` per turn — the per-invocation
  unlinkability `gaps-1 §(d)` calls missing.
- **Anonymous delegation = the ZK auth-chain** (tier 3 above): prove a legal CDT
  derivation path existed without revealing the path.

So privacy is **FieldVisibility ⊕ value-rib ⊕ (ZK-auth-chain + holder-blinding +
stealth + blinded-queue)** — not a subset, the full three-tier stack on existing
primitives.

---

## 6b. Multiagent + zkRPC = caps + the await family + the badge `[C/F]`

This is the **product surface** — `gaps-2 §(e)` correctly says it was compressed to one
`[F]` line. It is core, and it is *already assembled* from §3 (caps), §4 (await), and §6
(the badge / return-projection); the only genuinely-above-core piece is the concrete
daemon (see closing note).

- **An agent = a first-class principal holding caps.** Not a special type — a holder of
  `Authorization::Token` biscuits / `CapabilityRef`s, identified by its key. The MCP
  `dregg_create_agent` tool mints exactly this.
- **A zkRPC toolcall = a turn across a vat boundary returning result + badge.** It is
  the **return-projection** (§6 gap #2) composed with the **settled-call await face**
  (§4, the *backward* resolver): request → response + detached proof; the caller
  suspends on "the callee's `Obs` advanced past receipt R." The MCP submit/authorize/
  read round-trips (`node/src/mcp.rs`) already *are* this shape; the doc was behind the
  product.
- **Coordination = three await faces + discharge:** (a) **intent-market** = the
  ∃-resolver await (§4, "any filler satisfying P"); (b) **delegation-tree** =
  attenuated caps handed to sub-agents (the lossy `ρ_out`, §3) over MCP/A2A; (c)
  **settled-call RPC** = the backward await face above; (d) **discharge** for
  cross-trust 3rd-party caveats (§3).

**Honest badge semantics (the load-bearing constraint).** A returned badge attests
**(permitted) ∧ (effects-as-committed)** — a legal derivation existed (de-jure) and the
committed `Obs`-delta + per-class conservation hold (the value rib, §6.1). It does
**NOT** attest *de-facto authority* — what the holder can eventually cause is recovered
behaviorally from the log, never from the badge (§0, the `BA`-vs-`TP` split). A badge is
a value-bearing transition-attestation, **not** a grant of standing.

**The MCP server is the concrete agent interface** — ~46 `dregg_*` tools
(`node/src/mcp.rs`): `authorize`, `submit_turn`, `delegate`, `grant_capability`/
`revoke_capability`, `create_agent`, `post_intent`/`fulfill_intent`/`place_bid`,
`create_stealth_address`, `private_transfer`, `bilateral_action`, `issue_credential`,
`prove_*`/`verify_*`, `create_from_factory`. These are the surface syntax over which the
caps + await + badge core is exercised; they are *in* the core (the daemon hosting them
is not — closing note).

---

## 7. Proof architecture

dregg2's novelty = **PCA + IVC**. `[G/F]`

- **CCS as the one IR.** Keep all AIRs CCS-expressible as the portability hedge.
- **ProtoStar-style folding accumulator behind a `RecursionBackend` trait** —
  `MAX_DEPTH: Option`, `needs_cycle: bool`; **never an `additive_combine` method**
  (that forks into two IVC layers, `decisions §3`) → feeds a **WHIR-STARK seal
  compressor**; **lattice (Neo) for PQ**. `[G]`
- **Impossibility bound (honest):** there is **no unconditional / arbitrary-depth /
  NP-witness IVC** — **depth is a security parameter, a named assumption is
  required** (`decisions §0.2`). Recursion is a *deferrable feature*, NOT on the
  soundness-critical path. `[G]`
- **Leaf** = FRI/BabyBear/Poseidon2 (already PQ/hash-native) → WHIR later (cheapens
  the recursive verifier); **LogUp** lookups (not Lasso); **HidingFriPcs** for ZK
  (**ban FFT-type quotient splits** — the Haböck/Al-Kindi footgun). `[G/C]`

### 7.1 The step-complete turn statement (the soundness-critical object)

`StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` — soundness holds
**iff** every step attests *all of it* (a non-contractive step "permits a drifting
future" under coinduction — worse than an inductive local error). The **6-clause
auth-in-proof** statement (the Auth conjunct), each clause cross-PI-bound to the
canonical turn: `[G]`

```
key → delegation → policy-entailment → effect-fold → replay → cell-root-binding
```

PI surface (the entire trust boundary): `AIR_VERSION, OLD/NEW_COMMIT, EFFECTS_HASH
(re-derived in-circuit), AUTH_ROOT, ACTION_AUTHORITY_DIGEST, CONSERVATION_VECTOR
(per-class), TURN_HASH / ACTOR_NONCE / PREVIOUS_RECEIPT_HASH, CONSTRAINT_MANIFEST_HASH`.

---

## 8. Metatheory module map

`./metatheory` (Lean4, `leanprover/lean4:v4.30.0`, mathlib via local path). Style:
*spec-first, grind up* — every theorem stated day-1 with `sorry`; discharge Core +
Conservation first, the boundary law last (mirrors l4v). `[C]`

All **fourteen** modules **compile** against mathlib v4.30.0 (`lake build` = 783 jobs,
0 errors, ~70 `sorry` warnings = the spec-first obligations). The first six are the
sound-core; the latter eight are the multi-cell + distributed + privacy + coordination +
effects + lifecycle build-out (the wave). `[C]`

| Module | Status | Content |
|---|---|---|
| `Metatheory/Core.lean` | ✓ compiles, `sorry`'d | symmetric-monoidal cells/turns + conservation as a measure valued in **any `AddCommMonoid M`** (not `ℕ`): `count : Cell → M`, one law `count B = count A + val tag` (judgement 1) |
| `Metatheory/Resource.lean` | ✓ compiles, **no `sorry`** | the **resource-algebra (camera) tier**: `ResourceAlgebra` (partial CM + `valid` + `core`), `Fpu` (frame-preserving update = general conservation), proved `ℕ` camera + NFT non-duplication (`excl_no_dup`); `Auth` sovereign↔fragment sketch |
| `Metatheory/Laws.lean` | ✓ compiles, `sorry`'d | `Predicate ⊣ Witness` Galois connection + verify/find seam (`Verify`/`Searchable`) |
| `Metatheory/Authority/Positional.lean` | ✓ compiles, `sorry`'d | the l4v integrity lift = the vat-boundary law; `Integrity` case-split; `LossyMorphism` |
| `Metatheory/Confluence.lean` | ✓ compiles, `sorry`'d | **I-confluence (judgement 3)**: `IConfluent`, `Tier1Eligible`, `admits_sound`, `nonpairwise_escalation` |
| **`Metatheory/Boundary.lean`** | **✓ compiles, `sorry`'d** | **coinductive, A-style** (decided): `TurnCoalg`, `Sound`/`IsBisim`, `sound_of_step_complete`, `BoundaryRespecting` |
| **`Metatheory/JointTurn.lean`** | ✓ compiles, `sorry`'d | **cross-cell `⊗` (the load-bearing multi-cell layer)**: `SharedTurnId` (CG-2 pullback), `JointBinding` (CG-2⊗CG-5, the HYPOTHESIS), `joint_sound` (binding a premise, never derived), `joint_sound_needs_binding` + `tensor_not_final` (irreducibility: `νF₁⊗νF₂` not final), `atomicity_as_proof` (`will_succeed` prophecy = cumulative AND), N-ary `JointFamily` |
| `Metatheory/StepCamera.lean` | ✓ compiles, `sorry`'d | **step-indexed Iris camera** (higher-order/recursive resources = cells stating facts about other cells): `OFE`, `Later`/▶ (= Boundary's guard), `NonExpansive`, `Camera extends ResourceAlgebra,OFE` + extension axiom; `discrete_camera_of_RA` |
| `Metatheory/Finality.lean` | ✓ compiles, `sorry`'d | **judgement 2 (ordering/consensus)**: the 4-`Tier` lattice + `rank` order, `FinalityRule`, `tau_unified`, `tier1_requires_iconfluent` (→ Confluence), `crossTierJoin`/`commit_at_join_of_tiers`, `no_downgrade` |
| `Metatheory/Privacy.lean` | ✓ compiles, `sorry`'d | **three privacy tiers**: field (`project` hides private), value (`Commitment` homomorphic ⇒ `committed_conservation` — Pedersen opening of Law 1), graph (`StealthAddr`/`unlinkable`, `ZkAuthChain`, `BlindedSet`), `Nullifier` (anti-double-spend ⊗ holder-anonymity reconciliation) |
| `Metatheory/Coordination.lean` | ✓ compiles, `sorry`'d | **MPST / choreography**: `GlobalType` `G` → `project` → `LocalType`, `ProtocolCell` (coalgebra = `G`), `projection_sound`, `deadlock_freedom_by_design`, `iconfluent_fragment_crossgroup_free` (→ Confluence, the *separate* judgement), `privacy_by_projection` |
| `Metatheory/Await.lean` | ✓ compiles, `sorry`'d | **await family**: algebraic effects (`Op`/`Computation`), `OneShot`/`Linear` continuations (`one_shot_is_static`, `runtime_guard_is_double_spend` = the Dolan anti-pattern), `turnAsRollbackHandler`, the four faces (`zkpromise`/`discharge`/`intent`/`promiseGraph`) + `four_faces_unify` |
| `Metatheory/Liveness.lean` | ✓ compiles, `sorry`'d | **GC-as-cell-liveness**: cyclic `LivenessGraph` vs acyclic `CDT` (`refcount_ne_reachability` proved), `dead_undecidable` (= FIND/VERIFY seam) resolved by `Lease`, `gc_safety_local` (proved), `revocation_needs_consensus`, `crossvat_cycle_leaks` (impossibility, proved) |
| `Metatheory/Upgrade.lean` | ✓ compiles, `sorry`'d | **anti-brick `set_program`**: `AirVersion` pin, `UpgradeAuth` (proof | signature), `setProgramAdmissible`, `upgrade_never_bricks`, `stale_version_falls_back_to_signature`, `upgrade_is_intra_authority` (→ Positional) |

**Crypto-soundness is NEVER merged into the Lean law** — the binding/extractability
of `Verify P w` is a *circuit* obligation, discharged separately; the Lean law treats
`Verify` as a decidable oracle (`README §8`). **Bridge** = backend #8 of
`dregg-dsl-differential` (Lean = golden oracle; empirical cross-validation over
`sorry`'d regions, not certification). `[C]`

---

## 9. Build sequence

**#1 — SOUNDNESS-CRITICAL: AUDIT step-completeness.** Is `StepInv = Conservation ∧
Authority ∧ ChainLink ∧ ObsAdvance` *actually all four in-circuit*? Memory + the
candidate docs flag that **auth is checked outside the proof, intent-predicates are
unenforced, and graph-folding is flat (non-recursive)** — so it is likely **not**
step-complete today, in which case the bisimulation does not hold and *nothing
downstream is sound*. **The fix is step-completion, not recursion. Recursion is
deferred.** `[G/C]`

Then, in order (`decisions §7`):
2. **Step-complete the per-turn proof** — the 6-clause auth-in-proof statement +
   in-circuit effects-fold + per-class conservation + chain-link + obs-advance.
3. **Write the `RecursionBackend` trait** (`MAX_DEPTH`, `needs_cycle`, no
   `additive_combine`); route all IVC through it.
4. **PCS/Fiat-Shamir adversarial tests** (the 11-item checklist tied to Orion-1164 +
   Gemini-565); reconcile the FRI-param disagreement; set a soundness-bit target.
5. LogUp for range/auth; port `prove_full_turn` → `HidingFriPcs`.
6. Run M1 (FRI-verifier-in-circuit per-step cost) + M2 (in-AIR-Merkle gap) → decide
   the recursion-impl primary; interim = the ~80%-built Pickles port behind the trait;
   PQ target = lattice-IVsC.

---

## 10. What genuinely remains "above the core"

The gap analyses (`gaps-1`, `gaps-2`) mis-filed five things as strata above the core;
§§1.5, 1.6, 1.7, 6a, 6b fold them *in*. After that fold, only an **operational /
deployment shell** remains genuinely above the core — none of it changes the semantics:

- **the node daemon** — the running process that hosts cells + the MCP surface
  (`node/`); the host-as-trust-root is a *concept* in the core, the daemon is its impl.
- **gossip transport** — Plumtree spanning-tree / IHAVE-GRAFT-PRUNE / anti-entropy
  (`net/src/gossip.rs`); the core says "the CDT is gossiped," not *how*.
- **relay / operator economics** — bonded operators, hosted inboxes, computrons /
  metering, the 50/30/20 fee split (`relay_service`, `coord/budget.rs`); conservation
  (the value rib) is core, *incentives* are not.
- **on-chain settlement** — SP1→Groth16→EVM anchoring (`chain/`); reaching a *non-dregg*
  verifier is a transport concern, not a soundness one.

(Plus the genuinely-deferred: arbitrary-depth IVC recursion — a named security
parameter, §7 — and schema-DAG fork/merge migration, §5.)

**Honesty note — does the coinductive type cleanly absorb cross-cell ⊗ and GC?**
- **GC: clean for the acyclic CDT; the cyclic case is open.** Reachability is a
  *side-condition* on `ν` (§1.7) — the codata's well-foundedness predicate — and the
  drop-protocol is the backward face of the await family; no new categorical machinery,
  the `νC` just gains a "while reachable" qualifier that was always implicit. **But this
  is clean only on the acyclic derivation graph, where refcount-at-zero = unreachable.**
  On the *cyclic* live-reachability graph refcounting cannot detect a dead cycle, so
  collecting cyclic garbage needs a real mark-from-roots trace that the runtime does
  **not** yet have (§1.7). The single-cell `ν` framing does not by itself supply
  cycle-collection — that is a genuine open piece, not "implicit."
- **Cross-cell ⊗: mild strain, structurally honest.** The single-cell keystone
  `Cell = νC.µI…` does **not** literally contain the tensor; we *extend* it to
  `(C₁⊗…⊗Cₙ)` (§1.6). The monoidal Core (§2.1) carries `⊗` natively, so the
  extension is principled, and γ.2 *implements* it — but the **equalizer/pullback
  binding (CG-2 ⊗ CG-5) is a constraint on the tuple, not a clause derivable from a
  single cell's `step`.** It is a genuinely *bilateral* obligation that must be
  proven jointly. So: the type composes via `⊗` cleanly, but soundness of a cross-cell
  turn is **not** reducible to per-cell soundness alone — it needs the joint agreement
  binding as an irreducible extra. That is the one place the otherwise-single-cell
  coinductive frame is *extended* rather than *inhabited*; it is honest, not a defect,
  but it is the seam to watch.

---

## Appendix — candidate index (superseded by this doc)

- `cand-A-vat-coalgebra.md` — the coinductive runtime/soundness style (→ §1.3, §6, §8 Boundary).
- `cand-B-witness-pca.md` — soundness-by-verification, the badge, PCA+IVC (→ §1.2, §7).
- `cand-C-cap-distributed.md` — the cross-net CDT, seL4-across-the-net, LossyMorphism (→ §1.1, §3).
- Upstream: `00-synthesis.md`, `01/02/03-spine-*.md`, `pdfs/discoveries.md`, `pdfs/decisions.md`,
  `metatheory/README.md`, `metatheory/Metatheory/Authority/Positional.lean`.
