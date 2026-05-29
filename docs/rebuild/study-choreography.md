# Study — Grounding (and correcting) the dregg2 coordination layer in the choreography / session-type / I-confluence literature

> Target: `docs/rebuild/dregg2-multicell-privacy.md` §6 (the coordination layer) + `pdfs/discoveries.md`.
> Method: not a summary — test the §6 claims against the literature in `pdfs/`, refute the false ones with
> citations, and locate the genuine open problems. Tags: **[G]** grounded in a read paper, **[F]** forward,
> **[REFUTED]/[CONFIRMED]** = verdict on a §6 claim, **[MISSING]** = paper we should fetch.
>
> **Library reality check (done first, as instructed).** The session-type PDFs we hold —
> `sessions-as-propositions` (Lindley–Morris), `comparing-session-type-systems-linear-logic`
> (van den Heuvel–Pérez), `dependent-session-types-verified-concurrency` (Fu–Xi–Das),
> `girard-linear-logic-syntax-semantics` — are **ALL binary, propositions-as-sessions (linear-logic-derived)**.
> Grepped every PDF in `pdfs/`: **the word "choreography" appears in ZERO of them.** Honda–Yoshida–Carbone
> *Multiparty Asynchronous Session Types* (JACM 2016) and Montesi appear **only as bibliography entries**
> (in `comparing-…` and `dependent-…`), never as content. **We have NO MPST paper and NO choreographic-
> programming paper in the library.** Every §6 claim that leans on "MPST projection," "global type," or
> "choreography" is therefore currently **ungrounded in our corpus** — it rests on the author's external
> knowledge, not on a paper an agent can check here. This is the single most important finding for the
> reliability of §6 and it conditions everything below. (`coalgebraic-semantics-silva.pdf` IS present and
> gives the automata-as-coalgebra `X→F(X)` / bisimulation / final-coalgebra `νF` machinery used for claim #3,
> but it says nothing about session types.)

---

## Claim 1 (the load-bearing one): "Linear session typing captures I-confluence." — **[REFUTED]**

§6 says: *"a linear/affine session type already tracks the resource-coupling that determines I-confluence"*
and uses this to let the type system **statically classify** the I-confluent fragment that runs cross-group
free. **This conflates two orthogonal properties. It is false, and the conflation is dangerous because it
gates the headline "free cross-group coordination."**

**Precise separation.**

- **What linearity guarantees** [G, Girard; Lindley–Morris]: a *per-run, single-trace, sequential* resource
  discipline — every channel/resource is used **exactly once** (no contraction = no copy, no weakening = no
  drop), and dual endpoints are consumed in a well-bracketed order. Linearity is a property of **one
  process's use of its own resources along one execution**. Cut-elimination = communication; well-typing ⇒
  the *single session* doesn't deadlock and doesn't leak/duplicate a resource.

- **What I-confluence requires** [G, BEC §2.2 / Thm 3.1]: a property of **concurrent merge across replicas**:
  `T` is I-confluent w.r.t. invariant `I` iff for concurrent `Tᵢ ∥ Tⱼ` the updates **commute** *and*
  `I(S) ∧ I(S+uᵢ) ∧ I(S+uⱼ) ⇒ I(S+uᵢ+uⱼ)`. This quantifies over *many independent runs reconciled after a
  partition* — exactly the dimension linearity says nothing about.

**The counterexample is the author's own, and it is literally BEC's canonical one** [G, BEC §2.2 verbatim]:
two withdrawals `T₁,T₂` from a shared pool/account under invariant `balance ≥ 0`. **Each is perfectly
linear** — each consumes its own input capability once, copies nothing, drops nothing; a session/linear
type system accepts both. **Yet `{T₁,T₂}` is not I-confluent**: each preserves `balance≥0` alone, the merge
overdraws. BEC: *"if T₁ and T₂ both decrease the same user's balance, they are not I-confluent."* So
**linear ⇏ I-confluent**. (And the converse also fails: a monotone counter increment is I-confluent yet is
naturally *non-linear* — it's `Copy`/affine on the read side. The two properties are genuinely orthogonal,
not one-directional.)

**Does ANY type system statically capture I-confluence?** Not the session/linear-logic ones we hold, and
essentially **no, not as a session type**. I-confluence is a property of the **(transaction-set × invariant)
pair**, not of a single process's channel usage — BEC computes it as a *separate invariant-confluence
analysis* (per-transaction, per-invariant), and CryptoConcurrency confirms the hardness from the other
side: shared-account transfer has a **reduction from consensus** [G, cryptoconcurrency], i.e. enforcing the
coupled invariant is a *distributed-agreement* obligation, categorically not a typing one. The closest a
*type* gets is the BEC-derived **lattice side-condition already in `discoveries.md` §3.7 / `LEARNINGS-
ordering-consensus` artifact-B**: a cell may sit at tier-1 *iff* its state is a bounded join-semilattice
with invariant-preserving joins (`I(x)∧I(y)⇒I(x⊔y)`). That is **not** a session type — it's a typed
property of the **cell-state lattice + action set**, an invariant-confluence judgement à la BEC, run as a
soundness gate (`FinalityRule::admits`).

**Verdict / required correction to §6.** Keep the *conclusion* (a statically-classified I-confluent fragment
runs cross-group free) — it is sound and well-grounded — but **change its justification**. The classifier is
**NOT the session/linear type**; it is a **BEC-style invariant-confluence analysis over the step's
write-set and the touched cells' invariants** (the §3.7 lattice condition). The session type contributes the
*sequencing/duality* (Law 2, deadlock-freedom of the protocol) and conservation contributes linearity
(Law 1); **I-confluence is a third, independent judgement.** §6's parenthetical *"the session type does this
statically"* and *"a linear/affine session type already tracks … I-confluence"* must be struck and replaced
with "an invariant-confluence (BEC) analysis on each step's effect against the cell-state lattice does this
statically; the session type only fixes the order, conservation only fixes linearity." This keeps the
buildable form honest and removes a soundness trap (a coupled Σ=0 settlement is linear and would be wrongly
waved through as "free cross-group" if linearity were trusted to detect coupling).

---

## Claim 2: "MPST projection is partial + incomplete." — **[CONFIRMED, but UNGROUNDED in our corpus]**

True to the literature (external knowledge): classical MPST (Honda–Yoshida–Carbone) projects a global type
`G` to a local type `G↾p` via a **partial** function guarded by **mergeability/projectability** side-
conditions on branching (`⊕`/`&`); the classic merge operator rejects safe protocols where a non-active role
can't reconcile its continuations across branches — projection is **sound but incomplete** (rejects safe
`G`). The modern state moves the needle (synthesis-based / k-MC / automata-theoretic completeness results,
and "general/full-merge" projections recover more protocols), but **completeness is not free** and remains
an active area. **However: this rests entirely on papers we DO NOT HAVE.** Our corpus cannot witness a
single projection rule. *Which dregg2 coordinations are projectable* cannot be answered against the library —
flag as blocked pending the MPST fetch. **[MISSING: Honda–Yoshida–Carbone JACM 2016; a modern
completeness/automata-MPST paper, e.g. Scalas–Yoshida or k-MC.]**

## Claim 3: "An MPST local projection embeds as a coalgebra of `νF, F X = Obs × (AdmissibleTurn ⇒ X)`." — **[PLAUSIBLE; partially grounded]**

The coalgebraic half **is** grounded: `coalgebraic-semantics-silva.pdf` gives automata as coalgebras
`X → F(X)`, the final coalgebra `νF` as the greatest fixpoint / behaviour space, and **bisimulation** as
behavioural equality [G]. A local session type **is** standardly a (possibly recursive) communicating
automaton / labelled transition system — so presenting `G↾p` as a coalgebra of a polynomial functor is
faithful **in spirit**, and there IS a real literature on coalgebraic/automata semantics of session types
(communicating FSMs; coalgebraic session subtyping-as-similarity) — again **external, not in our corpus**.
The dregg2 functor `F X = Obs × (AdmissibleTurn ⇒ X)` is a **Moore/Mealy-flavoured** machine (emit an
observation, accept an admissible turn, recurse). The embedding `G↾p ↪ CellProgram` is plausible but **lossy
in two named ways**: (a) MPST's *typed channels / duality* (which endpoint, linearity of the channel) is not
visible in `Obs × (AdmissibleTurn⇒X)` — it must be re-imposed as an admissibility predicate, so the coalgebra
sees only "is this the next legal action," losing the *who-owns-which-endpoint* structure; (b) MPST
*asynchrony* (buffered sends, output/input reordering) collapses, since `AdmissibleTurn ⇒ X` is a synchronous
acceptance step. Both losses are exactly where claim #4 bites. **Verdict: a faithful behavioural embedding up
to the synchronous, single-port restriction; bisimulation gives the correctness criterion ("the cell
simulates the projection"). Genuinely buildable, but the loss must be stated.** **[MISSING: a coalgebraic /
communicating-automata MPST semantics paper to make this precise.]**

## Claim 4 (implicit in §1, used by §6): "A step can be an atomic N-cell JointTurn." — **[GENUINE EXTENSION / OPEN]**

Standard MPST and choreographies sequence **binary** interactions `p→q:T` (one sender, one receiver per
communication action); even "multiparty" means *many roles in the protocol*, **not one atomic synchronous
N-way rendezvous as a single step**. A dregg2 step is a **Mina-forest-shaped atomic N-cell JointTurn** — an
*equalizer/synchronous N-ary* interaction committing all-or-none (the §1 cumulative-AND prophecy). The
nearest prior art is *multiparty synchronisation* / *global rendezvous* in process algebra and the "atomic
multicast" line, but **encoding an N-ary atomic step as a primitive in a choreography (rather than
desugaring it to a sequence of binary sends) is not standard MPST** and is **not in our corpus**. Combined
with the partition impossibility of §7-(1), an *atomic synchronous N-ary cross-group step* is a real
extension of the choreographic model, **CONFIRMED OPEN**.

## Claim 5: "A choreography that statically splits an I-confluent (partition-progressing) fragment from a coupled (blocking) fragment, over Byzantine parties." — **[CONFIRMED OPEN / likely NEW]**

MPST and choreographies **assume reliable channels and honest, non-crashing parties**; progress/deadlock-
freedom are proved in that fault-free model. Crash-tolerant and fault-tolerant choreographies exist in the
research frontier (external knowledge), but **our library has zero choreography papers and the closest
fault-tolerant-protocol material is BFT/DAG (`velisarios`, `bullshark`, `narwhal`, `mysticeti`, `dyno`) and
BEC/CryptoConcurrency — none of which is a *choreography/session-typed* result.** A choreography whose
**static projection-time analysis partitions steps into a BEC-I-confluent partition-progressing fragment and
a consensus-coupled blocking fragment, over Byzantine parties**, is — to the best of the available evidence —
**not present in any read or referenced work, and is a genuine novel contribution of dregg2** (it marries
MPST projection with BEC's invariant-confluence iff-theorem and CryptoConcurrency's dynamic escalation). This
is the design's strongest original claim. **CONFIRMED OPEN.**

## Claim 6: "ZK / private choreographies — a party ZK-proves conformance to `G↾p` without revealing `G` or others' moves." — **[OPEN; strong adjacent grounding, no direct paper]**

In MPST the global type `G` is **public**; "privacy by projection" (a party sees only `G↾p`) hides *others'
local types from each other operationally* but does not give a **cryptographic** proof of conformance. The
ZK substrate to do this is well-grounded in our corpus — `kachina-private-contracts`, `uc-zk-smart-
contracts`, `streaming-zero-knowledge-proofs`, the Zcash-style commitment/nullifier pattern in §2 — but
**none of these is about proving conformance to a session/global type in ZK.** A protocol where a party
emits a ZK proof "my move is admissible under my projection of a committed `G`" without revealing `G` or
co-parties' moves is **a genuine gap / open problem**: state of the art has the ZK machinery and (separately)
MPST, but not their composition. **CONFIRMED OPEN.** (This is also the cleanest fit for dregg2's "graph"
privacy tier: the choreography structure itself is the thing hidden, proven via the cell's in-circuit
admissibility predicate.)

---

## Net assessment for §6 (corrections to apply)

1. **Strike the linearity⇒I-confluence justification** (§6 lines ~122 and ~127–8). Replace with: the
   I-confluent/coupled split is a **BEC-style invariant-confluence analysis** over each step's write-set vs.
   the touched cells' lattice invariants (the `discoveries.md` §3.7 / artifact-B condition), **not** a
   property the session/linear type detects. Session type = ordering (Law 2); conservation = linearity
   (Law 1); **I-confluence = a third independent judgement**.
2. **Add a corpus caveat to all MPST/choreography appeals in §6**: they currently cite no paper we hold;
   mark `[F, external]` until the MPST/choreography papers are fetched and an agent reads them.
3. Keep the *conclusion* of the I-confluent-fragment design — it is sound — and keep §7's honesty about the
   partition impossibility (it correctly matches BEC Thm 3.1 + CryptoConcurrency's consensus reduction).

## Confirmed-open vs prior-art (the 6)

| # | Claim | Verdict |
|---|---|---|
| 1 | linearity captures I-confluence | **REFUTED** (linear ⇏ I-confluent; BEC withdrawals counterexample; orthogonal properties) |
| 2 | MPST projection partial+incomplete | **CONFIRMED** by external knowledge; **UNGROUNDED in corpus** (no MPST paper) |
| 3 | local projection ⊑ cell coalgebra | **PLAUSIBLE**, coalgebra half grounded (Silva); lossy on duality + asynchrony |
| 4 | atomic N-ary JointTurn step | **GENUINE EXTENSION / OPEN** (MPST sequences binary; no atomic N-ary primitive) |
| 5 | partition/Byzantine-tolerant split choreography | **CONFIRMED OPEN / likely NEW** (no fault-tolerant choreography in corpus) |
| 6 | ZK/private conformance to projection | **CONFIRMED OPEN** (ZK ⟂ MPST both present, composition absent) |

## Papers we are MISSING and should fetch

- **Honda, Yoshida, Carbone — *Multiparty Asynchronous Session Types*, JACM 2016** (the MPST foundation;
  cited but absent). *Mandatory before any §6 claim about projection/global types is trustworthy.*
- **A modern MPST completeness / automata paper** — e.g. Scalas–Yoshida *Less is More* (POPL'19, MPST via
  CFSMs, full-merge / model-checking completeness) or a k-MC paper — for claims #2 and #3.
- **Montesi — *Choreographic Programming* (thesis / *Introduction to Choreographies*, CUP 2023)** — the
  choreography-as-program model and Endpoint Projection theorem (claims #4, #5).
- **A crash/fault-tolerant choreography paper** (e.g. Montesi et al. on choreographies with failures /
  fault-tolerant EPP) — directly tests claim #5's novelty.
- *(Nice-to-have)* a coalgebraic / communicating-automata session-type semantics paper for claim #3.

## The single most important open problem for dregg2's coordination layer

**A projection-time static analysis that, given a multiparty choreography `G`, partitions each step into a
BEC-I-confluent (partition-progressing, no atomic commit) fragment and a conservation-coupled (blocking,
atomic JointTurn) fragment, and proves the projection sound over *Byzantine* parties — i.e. the marriage of
MPST endpoint projection with BEC's invariant-confluence iff-theorem and CryptoConcurrency's dynamic
overspend-escalation.** This is the formal object §6 *describes* but does not have: it is unaddressed in the
entire library, would make "free cross-group I-confluent coordination" a *theorem* rather than a design
slogan, and is the foundation on which claims #1, #4, and #5 all rest. Everything else (ZK conformance #6,
coalgebraic embedding #3) is downstream of getting this static split right.
