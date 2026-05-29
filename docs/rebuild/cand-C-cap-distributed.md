# Candidate C — The Distributed Capability-Derivation-Tree (seL4 across the untrusted net)

> **One candidate architecture for dregg2.** Vision = **Robigalia, stated most
> literally**: take the seL4 capability system and see how far it extends across
> an untrusted global network. A persistent distributed OS where developers
> collaborate on untrusted code without getting hacked; checkpoint/restore/replay/
> debugger are native, not bolted on.
>
> **Center:** the **CDT extended across the network** is the primary object.
> Everything else (cell, turn, proof, consensus) is a way of *living in*,
> *traversing*, or *attesting* that tree. This document honors the corrected canon
> of `00-synthesis.md` + `pdfs/discoveries.md` + `pdfs/LEARNINGS-capability-boundary.md`
> and is **distinctly-dregg**, not an seL4 re-implementation: the seL4 reflection is
> a *lossy morphism stated as a theorem*, and the honest gap between *permission*
> and *authority* across the net is admitted, not papered over.

---

## 0. The thesis in one breath

seL4 proves a machine-checked **integrity theorem**: a subject modifies only what
its caps authorize (`LEARNINGS-capability-boundary.md` §F; the `part s ⤳ p` vs
`part s ⤳̸ p` case-split). That theorem rests on **one trusted kernel** mediating
every invocation. dregg2's whole question is: *what survives when you delete the
single kernel and spread the same authority structure across mutually-distrustful
hosts, content-addressing, and proofs?*

The answer, stated honestly up front: **permission survives; authority does not.**
The cross-net CDT can prove, soundly and locally, that *a legal derivation path
existed* (de-jure permission — Miller Table 8.1's `TP`, a static-graph fact). It
*cannot* prove what a holder can eventually *cause* (de-facto authority — `BA`,
behavioral, recovered only from the log), because a caretaker/forwarder makes the
static cap-graph **lie** (`discoveries.md` §3.6; LEARNINGS §A, §T3). So the CDT is
the **spine of permission**; **truth-is-the-log** is the spine of authority. That
split is not a defect of this candidate — it *is* its central, load-bearing
discovery, and the reason it is the most literal reading of "seL4 across the net."

---

## 1. Ontology — the primary object is the cross-net CDT

The **capability-derivation-tree** is one append-only, content-addressed partial
order of `(parent → child)` edges, each edge a **monotone attenuation**. This is
the same structure viewed two ways (the deepest collapse, `01-spine §1.1`):

- as a **cap graph** it is the seL4 CDT (CNode `Mint`/`Copy`/`Revoke`);
- as a **strand log** it is the blocklace (per-strand append-only causal DAG).

> **CDT ≡ strand log.** A capability *is* a derivation node; appending a turn *is*
> minting/exercising an edge. There is no second data structure.

The four kernel-object analogs, mapped (the literal seL4 carry-across):

| seL4 | dregg2 | grain |
|---|---|---|
| CNode / kernel object | **cell** | endpoint + the c-list cache of held `CapHash`es |
| invocation (`Call`/`Send`) | **turn** | the morphism; a bundle of cap *exercises* |
| CSpace / kernel ↔ thread | **vat / trust-root boundary** | the kernel↔network seam (host = trust-root) |
| `Mint` with reduced rights | **attenuation edge** | the *one* rule the system rests on |
| the kernel (single, trusted) | **(consensus + content-addressing + proofs)** | the de-centered mediator |

A `Cap` is identified by **its derivation, not its storage**:
`CapHash = H(canonical{root, target, authority, facet, caveats, parent, delta})`.
The slot/badge is a local handle (CSlot index ↔ `CapHash`), exactly as a c-list
slot is today — the slot/badge duality is the same pattern at two layers
(`01-spine §3.2`).

**Distinctly-dregg, not a paper re-impl:** seL4's CDT lives in trusted kernel RAM
on one machine. dregg2's CDT lives in an untrusted gossiped DAG across hosts and
*offline*, and so it must carry **the two seL4 properties as cryptography** where
the kernel is gone — which is §4's lossy-morphism theorem, the conceptual core.

---

## 2. Cell / turn / cap / proof under this lens

### 2.1 Cell = kernel-object-analog + the c-list cache
A cell is a CNode: the unit of state/lifecycle and the holder of a c-list
(`CapabilitySet`, kept as a *cache* over the CDT, not the source of truth). A cell
*mints a root cap whose facet is its full interface*; every access is an
attenuation of that root. `CellLifecycle` terminal objects, `FieldVisibility`,
`WitnessedReceipt` survive unchanged as cell-layer keepers (`01-spine §5.1`).
Within one host, many cells run sync-near (caps-as-caps); off-host they are
async-far (keys-as-caps) — the graduated membrane of `00-synthesis §2.1`.

### 2.2 Turn = invocation = a bundle of cap exercises (the rollback handler)
A turn is one run-to-completion invocation with **mutually-exclusive access to the
vat's state** (Miller ch.14; LEARNINGS §D). Mechanically it is **the rollback
handler** (`discoveries.md` §3.5; Plotkin-Power §6.8): outgoing effects are *held
until commit* — commit = replay the held log, abort = discard = a
conservation-preserving refund. This single rule realizes both ambient laws
(**conservation** = symmetric-monoidal `withhold Δ/◇`; **ordering** = which edges
compose into which strand = canonicity), and gives checkpoint/rollback/time-travel
"for free" (the seL4/EROS "vat incarnation" rollback, §5).

Conservation is **not** a cap exercise — it is a global per-turn invariant
(`Σ_k` a strong monoidal functor `(TurnCat,⊗,I) → (ℕ,+,0)`, constant off mint/burn;
`discoveries.md` §3.2). It rides **alongside** the CDT as a co-equal rib, *never
smuggled into a `Caveat::Custom`* (that is the "ioctl of dregg" failure, `01-spine
§7.2`). **Gap #1 folded:** per-asset value goes *into the proof* — the effect-fold
clause re-derives `Σ_k` in-circuit over the exercised effects, not as a host
commitment the AIR trusts.

### 2.3 Cap = the CDT node; eight auth modes dissolve into root-seals
`Authorization`'s eight variants collapse: there is **one** way to say "I'm
allowed" — *present a CDT path from a root I control to this exercise, plus each
edge's caveat discharge*. The variants become kinds of **`RootSeal`**
(`{CellMint, KeySeal, Sel4Reflected, SwissSeal}`) + caveat-discharge kinds. The
four cell-side gates collapse to one `WitnessedCondition` (binding-site + engine:
Datalog | WitnessedPredicate | **Await**); the `CaveatSet` is a *small closed* set
`{Expiry, Predicate, Rate, Finality}`.

### 2.4 Proof = the attestation that the CDT licensed the exercise (Predicate ⊣ Witness)
"Proof is truth" is *native* here, not a bolted-on conjunct: an exercise **is** the
traversal of an authorized arrow, and the proof's *subject* is "this is the value
of `eval` on a genuine CDT morphism" (`01-spine §2`). The **step-complete**
per-turn statement (`decisions.md` §0; `discoveries.md` §5 6-clause):

```
key → delegation-path → policy-entailment → effect-fold(Σ_k) → replay → cell-root-binding
```

binds, in-circuit, every edge as a legal attenuation (`child.facet ⊆ parent.facet
∧ child.authority ≤ ∧ child.caveats ⊇`) and every caveat as discharged. This is the
**witness** side of the `Predicate ⊣ Witness` Galois connection (`HeytingAlgebra`,
not a heavy adjunction): within a vat the predicate is the trivial witness; crossing
a vat boundary the witness becomes *mandatory* (§5 boundary law). The
proof-search/path-find is **undecidable** and lives in an untrusted plugin (the
deferred-prover); the verifier checks it cheaply — **TCB = verifier, never solver**
(`discoveries.md` §1, the VERIFY/FIND seam).

**Gap #2 folded — the await / return-projection face.** A far-reference invocation
returns a **promise**; a cross-host cap exercise that awaits a settled result is a
*suspended morphism* — `WitnessedCondition::Await` over the four faces
(zkpromise/discharge/intent/registry, `00-synthesis §3.2`). The **return-projection
+ settled-call await face** is the cross-vat dual of the held-until-commit handler:
the caller holds a promise-edge in *its* CDT; resolution appends the settling edge
and re-anchors the await against the returned value. One-shot (linear) continuation
typing makes conservation fall out as a corollary (`discoveries.md` §5).

---

## 3. How this realizes Robigalia *most literally*

**seL4 semantics carried across an untrusted net.** Three regimes for one
primitive, opted-into by *what an exercise touches* — not a property of the
substrate (`01-spine §3.3`):

1. **Intra-host (n=1 strand):** the host kernel/executor *is* the mediator —
   caps-as-caps, no proof, no gossip, instant finality. A `Sel4Reflected` cap on
   its home machine is a plain kernel `Call`; the log records it for *history*
   (orthogonal persistence), not agreement.
2. **Cross-host, point-to-point (handoff):** the cap **acquires a derivation
   proof at the boundary** — the receiving host verifies the proof *instead of*
   trusting a kernel it never shared. Two-party, store-and-forward, works offline
   (the BLE/two-phones case). This is the literal "seL4 cap, now proof-carrying,
   crossing an address-space it doesn't share."
3. **Multi-party contended resource:** only a balance/nullifier/singleton — a
   conservation-or-uniqueness claim — enters consensus (§6). **Revocation is the
   canonical case.**

**Developer collaboration on untrusted code = cap delegation across hosts with the
integrity guarantee preserved-where-possible and its loss stated where not.** A
developer hands a colleague an attenuated cap into a sandbox cell on an untrusted
host; the integrity property *holds intra-host* (the host kernel/executor confines
the borrowed code to exactly the minted authority — Doerrie's *local* confinement
test: inspect only the caps placed in the new cell, `LEARNINGS §G/4`); *across the
host boundary it degrades to permission-only* and the colleague's *actual*
behavior is recovered behaviorally from the receipt log (BA, §4). "Don't get
hacked" = **defensive consistency, fail-stop**: a crossing either yields a valid
witnessed turn or breaks the promise/receipt — never a wrong answer, never
guaranteed progress (Miller ch.5; LEARNINGS §T5). Corruption is contagious
**upstream only** (provider→client).

**Fork-as-sandbox = the collaboration primitive.** Forking a strand onto an
untrusted host "to evaluate in a container" mints a `ForkCap` scoping a
copy-on-write sub-CDT; **merge = re-root iff every edge stays a monotone
attenuation** of the advanced parent — merge conflicts *are* attenuation
violations, a principled rejection rule, not a CRDT tie-break (`01-spine §4.2`).

---

## 4. The metatheory entry (the conceptual core, two theorems)

Target = `./metatheory` (Lean4), the seL4 integrity theorem **lifted** off the
single kernel. The literal template is the l4v integrity proof (`~/dev/l4v`,
flagged unread — read before writing `Authority/Positional.lean`).

**(A) `Authority/Positional` — the vat-boundary law (integrity case-split lifted).**
The seL4 `part s ⤳ p` / `part s ⤳̸ p` dichotomy, with `subject → trust-root`,
`transition → turn`:

- *intra-vat* (`rootOf s = rootOf s'`): positional authorization — a mediator
  slot-read, `∃ cap ∈ caps` — admits the **trivial witness**; the turn mutates
  freely, no policy edge consulted (`¬ RequiresWitness`).
- *cross-vat* (`rootOf s ≠ rootOf s'`): admissibility ⇔ `Discharged P w`
  (`Verify P w = true`); a *specific authority edge* must license the crossing
  and the **witness side becomes mandatory**.

The crypto substitution is **literally replacing the positional ∃ with the
decidable verification** — a freely-copyable, verifier-checkable object, no
off-island mediator. Companion: `authority_confinement` (the trust-root is an
*upper bound*; no growth — `AuthorityBound (rootOf s) s' ≤ AuthorityBound (rootOf
s) s`). Existence proof it carries: Doerrie's axiom-free Coq confinement
(`mutable` over-approximates `mutated`, test local to minted caps).

**(B) `LossyMorphism` — the distinctly-dregg theorem, not a slogan.** The forgetful
functor Φ : ObjCap(Model 4) → KeyCap(Model 3) is faithful on `target`/`facet` but
**drops precisely Miller's Property F** (access-controlled delegation ⇒
confinement) **and Property E-in-practice** (composability ⇒ revocable forwarders):

```
caps_to_keys_drops_F : ∀ k : KeyCap, ¬ AccessControlledDelegation k   -- keys copy freely
caps_to_keys_drops_E : ∀ k : KeyCap, ¬ ∃ r, RevocableForwarder k r
```

> **structural unforgeability → cryptographic unforgeability; loss = revocation-by-
> construction + confinement-by-construction.** Φ⁻¹ (keys→caps) is defined *only
> relative to a mediator island* (a trusted minter re-establishes F).

This is the heart of "seL4 across the net": the same authority structure survives
the crossing **up to a precisely-named loss**. The two seL4 properties that made
the integrity theorem hold become the two properties the network cannot keep for
free. Stating the loss as a checked theorem — not a hand-wave — is what makes this
candidate honest. State both **coinductively** (`TurnCoalg`, `sound_of_step_complete`
as a bisimulation, the chain-guard as Birkedal's `▶`) so it covers non-halting
cells (`decisions.md` §2). **Caveat (in the README):** Lean certifies the *semantic*
loss; it does **not** establish that the STARK attests the morphism — that is a
separate circuit obligation, never merged into the law.

---

## 5. Checkpoint / replay (EROS orthogonal persistence + the log)

Native, not bolted on — this is the "persistent distributed OS" half of Robigalia.

- **The log is the inputs** (houyhnhnm orthogonal persistence; the
  `WitnessedReceipt` chain is *explicitly* "the persistence layer; the DB is the
  cache; the chain is the truth," `turn.rs:6-38`). State is *derivable* by replay.
- **Checkpoint = EROS pre-commit consistency check** (`LEARNINGS §H/5`): an
  inconsistent checkpoint lives forever, so check *before* commit; the
  **causal order of protection/authority events is sacred**, pure-data effects may
  journal out of order. This is the **cheap eager pin** (`previous_receipt_hash`,
  `00-synthesis §2.4`) given EROS's exact discipline — and it is the chain-guard
  `▶` of the coinductive soundness proof.
- **Restore / rollback / debugger = "vat incarnation"** — roll the vat back to a
  prior assumed-good state and replay the held log (Miller ch.14; the turn-as-
  rollback-handler, §2.2). A native debugger is *replay with breakpoints on
  edges*; time-travel is re-rooting the replay at an earlier receipt.
- **Replay across a vat boundary / on vk-rotation = re-prove from the retained
  log** (rejuvenation, `decisions.md` §5): always available because log-is-truth;
  inherits full non-malleability. *Inside* a vat, controlled malleability only.
- **Teleport** = ship `(id, head, rule)` + receipts over the shared DAG
  (zero-cost intra-fabric), with **capability-sealed serialization** (an exporting
  cell must not serialize authority it never held, `00-synthesis §2.4(2)`).

---

## 6. Consensus, finality, and the one globalism

The single trusted kernel is replaced by **(consensus + content-addressing +
proofs)**. Almost everything is local: single-owner/intra-host state never needs
consensus; shared state needs it **only on an actual overspend attempt**, and
conflict is *not pairwise* — escalation triggers are sum/coverage predicates over
the whole concurrent set (`discoveries.md` §4, CryptoConcurrency).

Finality is a **caveat on a strand's commit cap** — pluggable by construction
(`01-spine §4.3`): tier-1 causal-only (n=1, never blocks) → tier-3 Cordial-Miners
τ-BFT → tier-4 constitutional. The DAG carries all tiers; a block written under
tier-1 can be finalized under tier-3 later. **Well-formedness side-condition**
(BEC): a cell may select tier-1 *only if* its invariant is **I-confluent**
(`I(x) ∧ I(y) ⇒ I(x⊔y)`) — hash-keyed nullifier uniqueness qualifies; `balance≥0`
does not (a static type error otherwise; `discoveries.md` §3.7).

> **The only globalism is root-epoch agreement for revocation.** Revocation is the
> one op that wants consensus: a **negative discharge** — a STARK *non-membership*
> proof against an attested revocation root. It is the de-facto dual of the de-jure
> path-proof: the path says "permitted"; non-membership says "not since revoked."
> Everything else is local + content-addressed + proof-carrying.

---

## 7. Honest tradeoffs / risks

1. **Permission ≠ authority across the net (the decisive one).** The CDT proves
   de-jure `TP` (path-exists + legal-attenuation), *not* de-facto `BA` (what a
   holder can eventually cause). A caretaker/forwarder makes the static cap-graph
   lie. dregg2 must prove `TP`-class facts in-circuit and reason about `BA`-class
   facts **behaviorally, from the log** — and never market the path-proof as an
   authority proof (`discoveries.md` §3.6; LEARNINGS §T3). This is intrinsic to
   removing the kernel; it cannot be engineered away.
2. **Revocation needs consensus; local-first forbids instant global revocation.**
   A theorem, not a bug: a partitioned phone honors a revoked cap until it learns
   otherwise. Mitigation = **prefer short expiry + renewal** (auto-revoke needs no
   gossip); revocation is a tombstone reaching finality at the commit-cap's pace;
   the receipt records "exercised at staleness S" so a reconciler can *compensate*,
   not *prevent* (`01-spine §7.3`). Any design claiming clean local-first
   revocation is lying.
3. **Deltas l4v never modeled.** (a) **Dynamic labelling** — seL4's integrity is
   over a *static* policy `pas`; dregg2's CDT mutates (mint/fork/merge/teleport),
   and `sscc` requires cross-boundary channels never be *destroyed* (destruction is
   an observable bidirectional flow). Boundary-mutating ops must be modeled
   intra-trust-root *or* be authorized-logged-gated turns; the revocable-forwarder
   (disable, don't destroy) handles this gracefully (LEARNINGS §T4). (b)
   **Partial-turn liveness** — l4v never modeled non-termination/progress; dregg2's
   await family and cross-host promises can stall. We promise **only defensive
   consistency (fail-stop)**, never progress (LEARNINGS §T5); liveness is out of
   scope for the Lean law (`decisions.md` finality §).
4. **seL4 lattice-alignment is a partial functor, not an isomorphism.** dregg2 has
   18+ facet bits + rich witnessed-predicate caveats; seL4 has ~4 rights bits.
   kernel→dregg is faithful; dregg→kernel projects away everything richer than
   rights bits (caveats live in user-space on the Robigalia side). Document the
   non-reflected residue; don't imply parity (`01-spine §7.6`).
5. **Schema/interface evolution.** Bit-positional `EffectMask` is fragile under
   evolving per-cell interfaces. Fix = **content-addressed descriptors**
   (facet = canonical Set of effect Symbols; `AIR-id = H(canonical(schema_decl))`;
   Preserves), with lazy `migrate-on-read` + a transparency-and-conservation
   obligation on the migration (`discoveries.md` §5). Open: schema-DAG / fork-merge
   migration.
6. **The unaudited proving stack is the real engineering risk.** Soundness lives in
   **step-completeness**, not recursion (`decisions.md` §0): if the live AIR does
   not attest the full `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`,
   nothing downstream is sound. Recursion sits behind a swappable `RecursionBackend`
   trait (no `additive_combine`); leaf = FRI/BabyBear (PQ-native today), recursion's
   PQ-ness a deferred swap (lattice-IVsC target / 80%-built Pickles interim).

---

## 8. What's distinctly-dregg (not an seL4 paper re-impl)

- **The lossy reflection is a *theorem*, not a slogan** (§4B): Φ drops *exactly*
  Properties E and F; loss = revocation-and-confinement-by-construction; Φ⁻¹ needs
  a trusted minter. seL4 never had to state this — it never left the kernel.
- **The CDT is the spine, and CDT ≡ strand log** (§1): one append-only
  content-addressed structure is *both* the cap graph and the blocklace. seL4's CDT
  is trusted kernel RAM; dregg2's is an untrusted gossiped offline DAG that carries
  the two integrity properties as cryptography.
- **Permission-in-proof, authority-in-log** (§0, §2.4, §7.1): the de-jure/de-facto
  split is made into the architecture's seam, with revocation's negative-discharge
  as its dual — the honest content of "proof-is-truth-across, log-is-truth-within."
- **Consensus opted-into by what an exercise touches** (§3, §6): the single kernel
  is replaced by local-by-default + the one globalism (root-epoch revocation).
- **Per-asset value folded into the proof** and the **return-projection/settled-call
  await face** folded into the held-until-commit rollback handler (§2.2, §2.4) — the
  two gaps closed within the cap lens.

---

## 9. The minimal primitive set under this lens

1. **`Cap`** = `{root: RootSeal, target: CellRef, authority: AuthorityClass,
   facet: Interface, caveats: CaveatSet, parent: Option<CapHash>, delta: Attenuation}`,
   identified by `CapHash = H(canonical(Cap))`.
2. **`RootSeal`** = `{CellMint, KeySeal, Sel4Reflected, SwissSeal}` — the
   unforgeable origins; one summand is "the local kernel vouches."
3. **`Attenuation`** = the single monotone narrowing, versioned by
   `CapLatticeVersion` (= the AIR version; the only thing to freeze).
4. **`CaveatSet`** = small closed `{Expiry, Predicate(Witnessed), Rate, Finality}`;
   `Custom` quarantined as a smell.
5. **The CDT** = append-only content-addressed `(parent → child)` attenuation
   edges, backed by the blocklace = **the same structure as the strand log**.
6. **`DerivationProof`** = the step-complete proof that a turn's exercises are
   `eval` on genuine CDT arrows (auth-in-proof native).
7. **The vat boundary** = the kernel↔network seam where, per the boundary law, the
   witness becomes mandatory and Φ's loss is incurred.

…**plus two co-equal ribs the cap layer does *not* own:** **conservation**
(`LinearityClass`, a global per-turn monoid-hom invariant) and the
**consensus/finality** mechanism that resolves contention and revocation across
partitions. The verdict: capability is the spine of **permission**; it is *primary,
not total* — and that honesty is exactly what makes it the most literal extension
of seL4 across an untrusted net.

---

## 10. The keys-as-caps token layer — the PRIMARY cross-net cap representation

The keys-as-caps axioms (the vat-boundary law, `discoveries.md §4–5`) are not an annex here — under
this candidate they are *the cap layer itself once it leaves the kernel*. The concrete carriers are
`Authorization::Token { encoded, key_ref, discharges }` + `TokenKeyRef`
(`turn/src/action.rs:422–450`):

- **biscuit** (`eb2_…`, `TokenKeyRef::BiscuitIssuer`) = **cross-vat**, public-key (Ed25519)
  verifiable offline by anyone (UCAN-class, DID-rooted attenuation-down-a-chain).
- **macaroon** (`em2_…`, `TokenKeyRef::CellScopedMacaroon`) = **intra-vat**, cell-scoped HMAC — the
  near-reference convenience inside one host (`discoveries.md §6.3`: not third-party-verifiable).

**Under THIS candidate's center (the cross-net CDT), the token is the PRIMARY cross-net cap
representation — and `the biscuit delegation graph ≡ the distributed CDT`.** §1's collapse already
said CDT ≡ strand log; the third identity completes it: a biscuit's signed attenuation-chain *is* a
path of `(parent → child)` monotone-narrowing edges from a `RootSeal` (`BiscuitIssuer` = the
`KeySeal` origin) to the exercised node. A biscuit block = a CDT edge; `Mint`-with-reduced-rights =
appending an attenuated biscuit caveat. There is no separate token data structure to reconcile with
the cap graph — they are the same append-only content-addressed partial order, one rendered in
kernel RAM, the other in a signed offline credential.

**The lossy reflection IS the caps↔token conversion.** §4's Φ — caps-as-caps positional inside a
host, serialize to a biscuit/macaroon key-as-cap on the boundary (`ρ_out`), re-mint on entry
(`ρ_in`), lossy and **attenuation-only** — is *exactly* the act of emitting a token. Φ dropping
Property F (confinement) and E (revocable forwarders) is what it *means* for a c-list slot to leave
the kernel and become a freely-copyable key. The token layer is not adjacent to the LossyMorphism
theorem; it is its operational realization.

**Discharge = the await engine's authority-face** (§2.4's `WitnessedCondition::Await`): a 3rd-party
caveat `cav@Loc⟨cId,vId⟩` is a CDT edge whose license is *suspended* on a remote resolution — the
discharge **gateway** = the named resolver, the discharge **token** (`discharges`) = the resolution,
`bindForRequest = H(M'.sig :: M.sig)` = the binding-site. The caller holds a promise-edge in its own
CDT until the settling discharge edge appends.

**Revocation is the one globalism** (§6, restated in token terms): a **negative discharge** — a
STARK non-membership proof against an attested revocation root — the de-facto dual of the biscuit
path-proof (path says "permitted"; non-membership says "not since revoked"). Only **root-epoch
agreement** is global; every other token op is local + content-addressed + offline-verifiable.
