# STUDY — The Projection-Time Split (dregg2's #1 open problem, attempted)

> **Target (the frontier theorem).** A *projection-time static analysis* that splits a
> multiparty global type / choreography `G` into **(a)** a BEC-I-confluent,
> partition-progressing fragment and **(b)** a conservation-coupled, atomic-JointTurn
> fragment, **proven sound** — endpoint behaviour ≈ `G` — over **Byzantine** participants.
> Sub-problems D (atomic N-ary choreography step) and E (partition/Byzantine
> choreographies) reduce to it (`discoveries-2 §6`, `study-choreography` Claims 4–5).
>
> This is an honest *design attempt* — no code. It is the marriage of three literatures
> that do not cite each other: **MPST endpoint projection** ⊗ **BEC invariant-confluence**
> ⊗ **CryptoConcurrency dynamic escalation**. I mark each step `[G]` grounded-in-a-read-
> paper · `[F]` forward-design · `[T]` theorizing/conjecture. Where it is genuinely open I
> say so in-line; the new-vs-assembled ledger (§3) is deliberately conservative.
>
> **One-line thesis.** The split is **not** a session-type judgement and **not** a
> per-interaction property. It is a *segmentation of the global type's state space* (Lucy's
> **segmented invariant-confluence**, `[G]` interactive-checks-vldb19) computed against the
> conservation lattice, where each segment boundary is exactly a **CryptoConcurrency
> escalation point** (`[G]` cryptoconcurrency.pdf) and each escalated step is realized as a
> **JointTurn equalizer** (CG-2 ⊗ CG-5, `dregg2 §1.6`). Soundness is the **conjunction** of
> three existing theorems plus **one genuinely new lemma** — the *boundary lemma* gluing a
> coupled step's output to an I-confluent step's input.

---

## 1. The shared formal object

We pin ONE syntax `G` and ONE well-formedness judgement carrying THREE orthogonal
annotations. This is the object all of D/E and Claims 1/4/5 are about.

### 1.1 The annotated global type `G` `[F, built on G]`

Take the standard MPST global type (Honda–Yoshida–Carbone `[G]`, in the
less-is-more/Scalas–Yoshida revised form `[G]` to avoid the broken-consistency trap):

```
G  ::=  p →{q₁..qₘ} : ⟨ ℓ⟨v : τ, κ, ι⟩ ⟩ . G        -- N-ary interaction (one sender, m receivers)
     |  p →{q₁..qₘ} : { ℓᵢ⟨…⟩ . Gᵢ }ᵢ              -- branching (⊕ at p / & at each qⱼ)
     |  G₁ | G₂                                       -- parallel (independent sub-protocols)
     |  μX. G  |  X  |  end
```

This already departs from textbook MPST in **one** structural way, and it is the D
sub-problem: the interaction prefix is **N-ary** `p →{q₁..qₘ}` (one synchronous
all-or-none rendezvous over m+1 roles), **not** desugared to a sequence of binary
`p→q`. Standard MPST sequences binary interactions; an atomic N-ary step as a *primitive*
is **not standard** (`[G]` confirmed by `study-choreography` Claim 4 and the corpus —
"atomic multicast"/global-rendezvous is the nearest prior art and it is not a choreographic
primitive). We adopt it because a JointTurn over N cells **is** exactly this primitive
(`dregg2 §1.6`: `Turn ⊗ : C₁⊗…⊗Cₙ → …`). The N-ary prefix is the choreographic *surface
syntax* of the equalizer object.

Each interaction carries three independent annotations `⟨v : τ, κ, ι⟩`:

**(i) Conservation annotation `κ` (linear payloads, Move-style) `[G]`.**
The payload `v : τ` is tagged with a `LinearityClass` (`dregg2 §6.1`). For a linear class,
`τ` is a **resource type** in the Move sense (`[G]` move-resources-2004.05106: "created or
destroyed only by its declaring module; cannot be copied or dropped"). The interaction's
conservation obligation is the per-class sum invariant of the value rib: across the
interaction, `Σ_k(sent) = Σ_k(received)` for every linear class `k` (mint/burn the only
generators allowed to move the count, `dregg2 §2.1`). Affine classes (`[G]`
affine-rust-mpst-2204.13464: drop/cancel permitted) carry `Σ_k(sent) ≥ Σ_k(received)` and
must emit a conservative-DROP witness `Σ before = Σ after + Σ dropped` (`dregg2 §5`). This
is **Law 1**, attached per-interaction.

**(ii) I-confluence classifier `ι` on the interaction's write-set `[G]`.**
`ι` is a tag in `{IConf, Coupled, ⊥}` computed by a **BEC invariant-confluence analysis**
over `(write-set of the interaction) × (cell-state lattice of the touched cells) ×
(their invariants I)`. This is **NOT** derivable from the session type and **NOT** from `κ`
(`study-choreography` Claim 1 [REFUTED] — *linear ⇏ I-confluent*: two linear withdrawals
overspend; *I-confluent ⇏ linear*: a monotone counter merges but is not conserved). The
underlying judgement is BEC's: a transaction set `T` is I-confluent w.r.t. `I` iff, for
concurrent `Tᵢ ∥ Tⱼ` from a reachable `I`-state, the updates commute **and**
`I(S) ∧ I(S⊕uᵢ) ∧ I(S⊕uⱼ) ⇒ I(S⊕uᵢ⊕uⱼ)` (`[G]` BEC §2.2). This is **Law 3** (`dregg2 §2.3`),
the third, orthogonal judgement.

**(iii) Byzantine participant assumptions `[G]`.**
Following crash-stop MPST's **optional reliability assumptions** (`[G]`
mpst-crash-stop-2311.11851: "the entire spectrum of unreliability … using optional
reliability assumptions"), `G` is annotated with a **fault model** `Φ`: a per-role honesty
predicate and the failure mode each role may exhibit. We strengthen crash-stop to
**Byzantine** (a role may *deviate arbitrarily* from its local type, equivocate, withhold —
`[G]` BEC's adversary "may deviate from the specified protocol in arbitrary ways"). We carry
two reliability budgets, distinguished because the two fragments tolerate Byzantines
*differently* (the load-bearing asymmetry of §3): the I-confluent fragment is
**Sybil-immune** (any number of Byzantines, `[G]` BEC Thm 3.1), the coupled fragment needs a
**bounded** quorum (`< n/3` or a per-cell `½(n+f)` finality tier, `dregg2 §2.2`).

### 1.2 The well-formedness judgement `[F, on G]`

```
   Φ ⊢ G  wf       (well-formed under fault model Φ)
```

holds iff **all three** of:

1. **Projectability + boundedness** (`[G]` MPST: the syntactic merge side-condition, or the
   semantic PES counterpart of `[G]` semantic-wf-2404.00446 — *projectability ∧ boundedness*
   as Prime-Event-Structure properties). This is Law 2 (ordering/duality), unchanged from
   MPST except for the N-ary prefix.
2. **Per-interaction conservation `κ` checks** (linear/affine type discipline; decidable —
   one-time unfolding of `μ` is finite, `[G]` deadlock-freedom-cm13 "linearity is decidable
   on the one-time unfolding").
3. **A global I-confluence segmentation exists** (§2): the reachable `I`-state space of `G`
   admits a finite segmentation under which every interaction is *either* I-confluent within
   its segment *or* sits on a (consensus-guarded) segment boundary. This is the new
   well-formedness clause and it is the crux.

**Why three judgements, not "two laws + a session type."** `study-choreography`'s central
correction: I-confluence is co-equal and independent of conservation and ordering. The
well-formedness judgement therefore has three *separately discharged* premises. A `G` can be
projectable + linear yet **not** admit a sound segmentation (the coupled fragment straddles a
partition with no shared quorum — §4); that is a *well-formedness error*, surfaced statically,
exactly as `dregg2 §2.2`'s tier-1 eligibility is "a static type error" today.

---

## 2. The split, precisely — the 2-colouring rule

We 2-colour each interaction of `G`: **blue** = `{I-confluent / partition-progressing}`,
**red** = `{conservation-coupled / atomic-JointTurn}`.

### 2.1 The wrong rule, and why (conflict is NOT pairwise) `[G]`

The naïve rule — "colour an interaction red iff its write-set conflicts pairwise with
another concurrent interaction" — is **wrong** on both ends:

- **Too eager (the CryptoConcurrency lesson `[G]`).** Static pairwise conflict over-escalates:
  cryptoconcurrency.pdf explicitly contrasts itself with "earlier work … where conflicts were
  defined in a *static* way, i.e., *any potentially conflicting* concurrent operations incur
  the use of consensus." Two concurrent withdrawals from one account *conflict pairwise* but
  **need not** escalate — only when their *sum* would overspend. The rule must fire **on the
  actual conflicting/overspending set, dynamically**, not on the pairwise relation.
- **Conflict is genuinely not pairwise (the PES lesson `[G]`).** semantic-wf-2404.00446 models
  the protocol's true concurrency as a **Prime Event Structure** where the *conflict relation*
  is a primitive over events, not the transitive closure of a binary one. Overspend is an
  **N-ary** predicate: `{T₁,T₂,T₃}` can each be pairwise-fine yet jointly violate `balance ≥ 0`.
  I-confluence (BEC §2.2) quantifies over the **whole** concurrent transaction set `T`, not
  pairs. So the colouring is a property of *segments of the state space*, not of *edges between
  interactions*.

### 2.2 The colouring rule — segmented invariant confluence `[G/F]`

The right object is Lucy's **segmented invariant confluence** (`[G]`
interactive-checks-vldb19): *"divide the set of invariant-satisfying states into segments,
with a restricted set of transactions allowed in each segment. Within a segment servers act
without coordination; they synchronize only to transition across segment boundaries."*

> **Colouring rule (the split).** Compute a segmentation `𝒮 = {S₁,…,S_r}` of `G`'s reachable
> `I`-states (under conservation invariant `I = ⋀_k (Σ_k preserved) ∧ (cell invariants)`).
> For an interaction `a = p →{q⃗} : ⟨v:τ, κ, ι⟩` evaluated in segment `Sⱼ`:
>
> - **BLUE (I-confluent / partition-progressing)** if, *within `Sⱼ`*, `a`'s write-set is
>   I-confluent w.r.t. `I` — i.e. `a` commutes with every other in-segment interaction and
>   the merge preserves `I` (`I(x)∧I(y) ⇒ I(x⊔y)`, `dregg2 §2.3`). It runs **cross-group,
>   partition-tolerant, with NO atomic commit** (causal/CRDT, tier-1).
> - **RED (coupled / atomic-JointTurn)** if `a` *crosses a segment boundary* — i.e. it can
>   move the state from `Sⱼ` to `Sₖ`, which is precisely where the in-segment restriction
>   that made the others blue no longer holds. The boundary crossing is the **escalation
>   point**: it is realized as an atomic JointTurn (CG-2 ⊗ CG-5) and gated on the actual
>   conflicting set (CryptoConcurrency: escalate *only when* the concurrent set on the
>   boundary would violate `I`, e.g. would overspend).

The two literatures fuse cleanly because they are the same idea from two sides:
- **Bailis/Lucy** says *where* the boundary is (the static segmentation of the I-state space;
  decided by the interactive procedure or the automatic `merge-reducibility` sufficient
  condition, §4.4).
- **CryptoConcurrency** says *when to pay at* the boundary (dynamically, only on the actual
  overspending set; otherwise even a boundary-crossing set proceeds in parallel if it
  doesn't exhaust the invariant).

So a RED interaction is **statically** marked "may need escalation" (it touches a coupled
write-set / boundary), and the JointTurn it compiles to is the mechanism that **dynamically**
decides — via the cumulative-AND prophecy (`dregg2-multicell §1`) — whether the *actual*
concurrent set conserves; if it does, the atomic step still commits without external
consensus, exactly CryptoConcurrency's fast path. The two-colouring is therefore *necessary
condition* marking, not *runtime decision*: blue = provably-never-escalates,
red = escalation-machinery-present-here.

### 2.3 What "partition-progressing" buys (the headline) `[G]`

By BEC Thm 3.1 (`[G]`, iff), the **blue** fragment can be implemented with a fault-tolerant
algorithm ensuring eventual consistency **under arbitrarily many Byzantine-faulty replicas**
— it *never blocks*, never invokes consensus, tolerates partitions and Sybils. This is the
"free cross-group I-confluent coordination" of `dregg2-multicell §6`, now a *consequence of a
theorem* rather than a slogan: it holds for exactly the interactions the colouring paints
blue, and BEC proves blue ⟹ coordination-free is **iff** (so the colouring is tight — no blue
interaction wastes a JointTurn, no red one is unsafely waved through).

---

## 3. The soundness theorem to prove (+ what-extends-what, new-vs-assembled)

### 3.1 Statement `[F/T]`

> **Theorem (Split-EPP soundness — to prove).** Let `Φ ⊢ G wf` with 2-colouring
> `(G_blue, G_red)` from §2, and let `EPP(G) = ∏_p (G ↾ p)` be the endpoint projection.
> Define the dregg2 realization `⟦G⟧ = (blue interactions ↦ CRDT/tier-1 cell turns) ⊗
> (red interactions ↦ JointTurn equalizers, tier = join of touched cells' tiers)`. Then for
> every run of `⟦G⟧` against an environment in which **honest** roles follow `G ↾ p`:
>
> 1. **(EPP correspondence)** the externally-observable behaviour of `⟦G⟧` is
>    weak-bisimilar to the behaviour of `G` — *endpoint behaviour ≈ `G`* — up to the
>    synchronous/single-port loss noted below;
> 2. **(blue never blocks)** every `G_blue` interaction is live under partition and under
>    arbitrarily many Byzantine roles (BEC liveness + Sybil-immunity);
> 3. **(red is atomic)** every `G_red` interaction commits all-or-none, conserving every
>    linear class, under the bounded fault model `Φ_red` (`< n/3`), and is **safe** (never
>    violates `I`) even when its liveness stalls under partition;
> 4. **(boundary soundness — the new part)** the composition is sound: a red step's committed
>    output feeds a blue step's input without breaking I-confluence of the blue segment, and a
>    blue step's merged output never silently moves the state across a red boundary
>    un-escalated.

### 3.2 What each half *extends* `[G]`

| Half of the theorem | The existing result it extends | How it extends |
|---|---|---|
| **(1) EPP correspondence** | **Deadlock-freedom-by-design EPP Theorem** (`[G]` deadlock-freedom-cm13, Thm 3 + Cor 1/2): a linear, well-typed choreography's EPP is in operational correspondence with `G` and is deadlock-free *by construction*. | Extends the *target* of projection from π-calculus threads to **dregg2 cells (coalgebras `νF`)**, and the *failure model* from fault-free to Byzantine via crash-stop MPST's reliability-assumption machinery (`[G]` mpst-crash-stop-2311.11851: "sound and complete correspondence between global and local type semantics … even in the presence of crashes"). We replace crash-handling branches with **escalation branches** and strengthen crash → Byzantine on the red fragment only. |
| **(2) blue never blocks** | **BEC iff-theorem** (`[G]` BEC Thm 3.1): a BEC algorithm tolerating arbitrarily many Byzantines exists iff all transactions are I-confluent w.r.t. all invariants. | Extends BEC from a *flat transaction set* to the **I-confluent fragment of a projected choreography** — i.e. BEC's "I-confluent portion can be implemented without Sybil countermeasures" (verbatim) is lifted to "the blue projection of `G`." This is essentially *application* of BEC, not extension; the only new content is that the fragment is *carved out by a session-type projection*. |
| **(3) red is atomic** | **A BFT-broadcast / atomic-commit result** + **Mina's cumulative-AND prophecy atomicity** (`dregg2-multicell §1`, `[G]` ADOPT-from-Mina) over a Byzantine quorum (`[G]` bft-web-services-2507.08281's L1 BFT consensus / the τ-BFT tier of `dregg2 §2.2`). | Extends single-ledger forest-atomicity (Mina) to **per-cell tier-local commits gated on a shared aggregate proof** (the divergence already in `dregg2-multicell §1`); and extends CryptoConcurrency's *single-account* consensusless-until-overspend to a **choreographed N-ary** boundary crossing. |
| **(4) boundary soundness** | *(nothing directly)* | **GENUINELY NEW** — see §3.3. |

### 3.3 New vs assembled — the honest ledger `[T]`

**Assembled (each half is a known theorem, instantiated):** EPP correspondence (cm13 + crash-stop), blue liveness (BEC), red atomicity (Mina/BFT/CryptoConcurrency). None of these three is new mathematics; the contribution at this layer is *that they compose over one `G`*.

**Genuinely new — three things:**

1. **The colouring rule itself as a projection-time analysis** `[T]`. Segmented
   invariant-confluence (Lucy) is a *database replication* technique over a flat object; no
   one has computed it as a **side-condition of MPST endpoint projection** that *splits the
   projected local types* into a coordination-free and a coordinated sub-type. The marriage
   "segmentation boundary = choreographic interaction that escalates to a JointTurn" is, to
   the corpus's knowledge, **not in any read or referenced work** (`study-choreography`
   Claim 5 [CONFIRMED OPEN / likely NEW]).

2. **The boundary lemma (4)** `[T]` — *the* novel obligation, and the one most likely to be
   hard or to fail (§4.2). MPST gives no account of two *fragments with different consistency
   models* meeting at an interaction; BEC has segments but no projection/duality; neither
   addresses the **interface contract** between a coupled step and an I-confluent step. This
   lemma must show: (a) a red step's post-state lands inside a single blue segment (so the
   blue fragment downstream is I-confluent *from that state*), and (b) merging concurrent blue
   outputs cannot reach a red boundary that was not itself escalated (no "I-confluent drift
   across a coupled invariant"). This is the unique new theorem.

3. **Byzantine endpoint projection of the split** `[T]` — proving correspondence (1) when a
   *malicious* participant deviates from `G ↾ p`. MPST/crash-stop assume honest-or-crashed,
   not arbitrary deviation; the soundness argument here is **not** a session-type subject-
   reduction (a Byzantine can't be type-checked) but a **verification** one (§4.1). Treating
   conformance as a checked witness rather than a typing premise is the dregg2-specific move
   (`dregg2 §1.2`) and is new *in the choreographic setting* (`study-choreography` Claim 6
   [CONFIRMED OPEN]).

**Bottom line:** the *theorem's halves* are assembled; the *coloring analysis*, the
*boundary lemma*, and *Byzantine-EPP-by-verification* are new. The honest framing is "a new
**glue theorem** binding three existing results, whose glue (lemma 4) is the actual research
content."

---

## 4. The hard parts / where it might fail

### 4.1 Byzantine endpoint projection — a malicious role deviating from `G ↾ p` `[T, open]`

EPP's correspondence (cm13, crash-stop) assumes honest endpoints (or honest-or-crashed). A
**Byzantine** role can send a message its local type forbids, equivocate (different messages
to different receivers), or forge a branch. Three layered defences, none free:

- **Verification, not typing (`dregg2 §1.2`).** Conformance to `G ↾ p` is recovered as a
  *checkable witness*: each turn carries a proof that the sender's action is admissible under
  the (committed) projection — the cell's in-circuit admissibility predicate (`dregg2 §1.5`).
  A Byzantine can deviate *only* by producing an action that **fails** the receiver's
  admissibility check, which the receiver rejects. This converts "subject reduction under
  Byzantines" (impossible — you can't type a liar) into "every accepted action satisfies the
  projection by construction." **This is the only viable route** and it is `[T]`.
- **Equivocation.** Caught by Byzantine causal broadcast for the blue fragment (`[G]` BEC's
  substrate: hashes/Merkle DAG make a divergent history detectable; equivocation is a
  detectable fork). For the red fragment, by the BFT quorum (`< n/3`, `[G]`
  bft-web-services-2507.08281).
- **The residual that may sink it `[T]`.** A Byzantine *receiver* in a blue interaction can
  refuse to merge — but BEC's Sybil-immunity (Thm 3.1) means honest replicas still converge;
  the malicious node only harms *itself* (it diverges from the canonical I-state). For a red
  interaction, a Byzantine *participant* of the JointTurn can withhold its CG-2 share to stall
  the atomic step — but **safety** is preserved (the aggregate AND never reaches true), only
  **liveness** is lost, which is the §4.3 partition problem anyway. **Open question:** can a
  Byzantine *straddle* the boundary — drive the honest parties to *believe* a coupled step is
  blue (I-confluent) when it is not — by lying about its write-set? If the write-set is part
  of the *committed* `G` and the colouring is computed from `G` (not from runtime claims),
  no: the colour is fixed at projection time. This is the argument that the *static* split is
  what saves Byzantine soundness — **conjecture, to verify in the minimal theorem.**

### 4.2 The fragment boundary — a coupled step feeding an I-confluent one (lemma 4) `[T, open]`

The genuinely hard composition. Concretely (the failure to rule out): a red settlement commits
`balance := balance − amount` (crosses the segment boundary `balance ≥ amount` → `balance ≥ 0`);
a downstream blue step appends to a CRDT log keyed on the new balance segment. If the red commit
is **tier-3** (BFT-finalized) but the blue step runs **tier-1** (causal) and *races* the
finalization, the blue step may observe a *pre-commit* balance segment and append something the
post-commit segment makes invariant-violating. The defences:

- **The cross-tier rule (`dregg2 §2.2`):** "a turn commits at the *join* of its written cells'
  tiers; effects held until the join-tier commits; no finalized value downgrades." So a blue
  step **causally dependent** on a red commit inherits a *happens-after* edge and cannot
  observe the pre-commit segment. This is exactly the well-bracketing the *session type* (Law
  2) already enforces: in `G`, the blue interaction is *sequenced after* the red one, so its
  projection has an input dependency on the red commit's receipt. **The session order is the
  thing that makes lemma 4 provable** — it pins the boundary crossing to a point in the causal
  order both fragments respect.
- **Where it might genuinely fail `[T]`:** when the blue step is *concurrent* with the red step
  in `G` (a `G₁ | G₂` parallel where `G₁` is blue and `G₂` is red and they share a cell). Then
  there is no session-order edge to lean on, and lemma 4 reduces to: *does the blue merge
  preserve `I` across a concurrent red boundary crossing?* This is **false in general** (it is
  literally the overspend counterexample), so the well-formedness judgement (§1.2.3) must
  **reject** such `G` — a parallel composition that shares a cell across a colour boundary is
  not well-formed unless the shared write-set is itself I-confluent. This is a real
  *restriction on expressible choreographies*, and pinning its exact statement is open.

### 4.3 Partition liveness of the red fragment (the impossibility, restated honestly) `[G]`

Not a bug — a wall. `dregg2-multicell §7-(1)`: an atomic JointTurn straddling **disjoint
reference-groups** under partition cannot be both safe and live (2PC blocks; 3PC/Paxos-commit
need a shared quorum disjoint groups lack). The split *contains* the damage to the red
fragment only (blue is partition-progressing by BEC), but it does **not** remove it. The
theorem's clause (3) therefore promises **safety always, liveness only under the bounded
fault model + non-straddling-partition**. Honest and final: *atomic-cross-group ∧
partition-tolerant ∧ live is impossible* (`[G]` the CAP/CryptoConcurrency consensus-lower-
bound) — the split's value is making the *fraction* that hits this wall as small as the
colouring allows, and BEC proves that fraction is *exactly* the non-I-confluent one (tight).

### 4.4 Is the colouring decidable? `[G/T]`

**No, not in general — and the paper says exactly why, with the standard fix.** `[G]`
interactive-checks-vldb19: "a general-purpose [invariant-confluence] decision procedure is
impossible because determining the invariant confluence of an object is **undecidable** in
general." The split inherits this. Three honest responses, all from the corpus:

- **Sound-and-automatic sufficient condition.** Lucy's **merge-reducibility** is *checkable
  automatically* and covers strictly more than invariant-closure (`[G]`). Use it as the
  default colourer: anything provably merge-reducible → blue; everything else →
  conservatively red. This is **sound** (never paints an unsafe interaction blue) at the cost
  of **incompleteness** (some safe interactions are needlessly red) — exactly MPST's own
  sound-but-incomplete projection trade-off (`[G]` less-is-more; `study-choreography`
  Claim 2). The two incompletenesses *stack*, which is fine: both fail safe.
- **Interactive decision procedure** for the cases merge-reducibility can't settle (`[G]` Lucy's
  human-in-the-loop procedure), used at design time to *certify* a blue colouring.
- **Bounded fragment.** For the linear/affine conservation invariants specifically (the value
  rib, `Σ_k = const`), the I-state space is a system of **linear constraints over integers**,
  for which I-confluence *is* decidable (`[G]` Lucy handles "linear constraints on integers"
  in < 0.5s). So for dregg2's *headline* invariant (conservation), the colouring **is**
  decidable; undecidability bites only for arbitrary custom invariants (`Custom` constraints,
  `dregg2 §1.5`), where we fall back to merge-reducibility-or-red.

---

## 5. A minimal first theorem (the smallest non-trivial instance)

### 5.1 The choreography: 3-party transfer-with-escalation `[F]`

Roles: **Buyer `b`**, **Seller `s`**, **Escrow/asset-owner `e`** (the asset-A owner-cell,
`dregg2-multicell §1` token-owner-as-co-participant). Invariant `I ≡ bal_b ≥ 0 ∧ bal_s ≥ 0`,
asset A linear (`κ = linear`).

```
G_xfer =
  b →{e,s} : Offer⟨amt : A_linear⟩ .          -- (1) post an offer  [BLUE: append, monotone]
  s →{b,e} : { Accept .                        -- (2) seller chooses [BLUE: I-conf branch select]
                 e →{b,s} : Settle⟨amt : A⟩ .  -- (3) atomic transfer [RED: crosses bal_b boundary]
                 b →{e,s} : Receipt . end       -- (4) ack receipt   [BLUE: append]
             | Reject . end }                   -- [BLUE]
```

**Colouring** (by §2.2): (1) Offer = append to an intent-log, monotone ⇒ **blue**. (2) Accept/
Reject = branch selection that writes only `s`'s local choice ⇒ **blue**. (3) Settle =
`bal_b −= amt; bal_s += amt`, which can cross the segment boundary `bal_b ≥ amt` (overspend if
`b` issued concurrent Settles) ⇒ **red**, the lone escalation point. (4) Receipt = append ⇒
**blue**.

So `G_xfer` has *one* red interaction. Its segmentation `𝒮 = { S_funded : bal_b ≥ amt,
S_spent : bal_b ≥ 0 }`; Settle is the only `S_funded → S_spent` boundary crossing; everything
else is intra-segment-blue.

### 5.2 Mapping to the JointTurn (CG-2 ⊗ CG-5) `[G, dregg2 §1.6]`

The red Settle compiles to a **2-cell JointTurn** over `(cell_b ⊗ cell_s)` with `e` as the
asset-A owner co-participant (3 rows in the aggregate AIR):

- **CG-2 (turn-identity pullback):** all three cells' per-cell step-proofs commit to the same
  `TURN_HASH / EFFECTS_HASH / PREVIOUS_RECEIPT_HASH` — Settle's proof for `cell_b` is valid
  *only* as part of *this* JointTurn (no solo replay). This is the equalizer/pullback over the
  shared turn-id (`dregg2 §1.6`).
- **CG-5 (cross-side existence / conservation):** the signed half-edge `−amt` on `cell_b` has
  its matching `+amt` on `cell_s`; the balance sum over committed (Pedersen) amounts is `0`
  (`bilateral_aggregation_air`, `[C]` `dregg2 §1.6`). This is the conservation equalizer.
- **Atomicity** = the cumulative-AND prophecy over the 3 rows (`dregg2-multicell §1`), **not**
  a 2PC. The escalation (CryptoConcurrency): if `b` has no concurrent Settle, the aggregate
  commits at tier-1-join without external consensus; only a *concurrent* Settle set that would
  drive `bal_b < 0` forces the boundary's BFT quorum.

The blue interactions (1,2,4) are *not* JointTurns — they are single-cell tier-1 turns
(`Cell → Obs × (AdmissibleTurn ⇒ Cell)`, `dregg2 §1.5`), partition-progressing.

### 5.3 The theorem to attempt (Lean / paper) `[F]`

> **Minimal Split-EPP soundness.** For `G_xfer` with the §5.1 colouring under fault model
> `Φ` (`b,s` may be Byzantine; the escrow quorum is `< n/3`):
> 1. `EPP(G_xfer)` is weak-bisimilar to `G_xfer` for honest-conforming runs;
> 2. interactions (1)(2)(4) are live under partition and arbitrarily many Byzantines;
> 3. the Settle JointTurn (3) is atomic + conserves A under `Φ`, safe even when partitioned;
> 4. **(boundary)** the post-Settle state lands in `S_spent`, and the Receipt-append (4)
>    is I-confluent *from `S_spent`* — i.e. lemma 4 holds for this `G` because (4) is
>    session-ordered *after* (3) (no `G₁|G₂` concurrency across the colour boundary).

**Why this is the minimal non-trivial instance.** It has (i) ≥ 2 blue and exactly 1 red
interaction (so the split is non-degenerate), (ii) a conservation-coupled write-set (so red is
forced by Law 1 ∧ Law 3, not Law 2), (iii) a real segment boundary (so segmented-I-confluence
is exercised), (iv) a clean session-order edge from red→blue (so lemma 4 is *provable* here —
the hard concurrent case §4.2 is deliberately excluded, to be attempted second), and (v) it
**is** dregg2's canonical `bilateral_action`, so the JointTurn target already exists in code
(`dregg2-multicell §1`, `[C]`). In Lean it slots into the spec'd `Boundary.lean` `JointTurn`
equalizer object: prove `joint_sound : (∀i, StepComplete Cᵢ) → JointBinding(CG-2 ⊗ CG-5) →
Sound(Settle)` for clause 3 (binding as premise, never derived — `dregg2-multicell §5`), and a
new `Confluence.lean` (the gap-0 module) discharges the blue clauses 1–2 + the boundary clause 4
via the join-semilattice + invariant-preservation judgement.

---

## Honest closing — what is conjecture

- The **colouring rule** (§2.2) is a *forward design* fusing two grounded techniques
  (segmented-I-confluence `[G]` + dynamic escalation `[G]`); their fusion as a projection-time
  analysis is `[T]` — unread in the corpus, plausibly new.
- The **boundary lemma** (§3.3 #2, §4.2) is the actual research content and is **conjectured**.
  It is provable in the session-ordered case (the minimal theorem leans on exactly this), and
  is **conjectured false / a well-formedness restriction** in the parallel-shared-cell case —
  pinning that boundary is open.
- **Byzantine EPP** (§4.1) via verification-not-typing is `[T]`; the claim that the *static*
  colour (fixed at projection from the committed `G`) is what immunizes the split against a
  Byzantine lying about its write-set is a conjecture the minimal theorem is designed to test.
- **Decidability** (§4.4) is honestly *no in general* (`[G]` Lucy), *yes for the conservation
  (linear-integer) invariant* (`[G]`), with merge-reducibility as the sound-incomplete
  automatic colourer everywhere else. The two incompletenesses (MPST projection +
  I-confluence) stack and both fail safe.
