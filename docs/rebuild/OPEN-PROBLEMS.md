# dregg2 — OPEN PROBLEMS (the research-grade register)

> **Status:** the companion to `ROADMAP.md`. These are **NOT** "just implement it"
> tasks — they are open research problems, genuine impossibilities, and corpus gaps.
> The roadmap's phases are buildable; these are the things a next agent must **not**
> mistake for engineering. Several are confirmed-open against the entire `pdfs/`
> library (see `study-choreography.md`, `study-consensus.md`, `study-gc.md`,
> `study-mina-relink.md`, `study-category.md`); some are genuine impossibilities (the
> price of having no global ledger).
>
> Tags: `[OPEN]` research-grade open problem · `[IMPOSSIBLE]` a proven/forced
> impossibility (design around, don't "fix") · `[GAP]` corpus gap (a paper we lack).

---

## #1 — The projection-time three-judgement split `[OPEN]` (the coordination layer's central missing theorem)

**The object:** a projection-time static analysis that, given a multiparty
choreography `G`, partitions **each step** into

- a **BEC-I-confluent** fragment (partition-progressing, NO atomic commit), and
- a **conservation-coupled** fragment (the blocking atomic JointTurn),

and proves the projection **sound over Byzantine parties**. It is the marriage of
**(a)** MPST endpoint-projection ⊗ **(b)** BEC's invariant-confluence iff-theorem ⊗
**(c)** CryptoConcurrency's dynamic overspend-escalation.

**Why it is open, not engineering.** I-confluence is an **independent third judgement**
— orthogonal to both conservation (linearity, Law 1) and ordering (the session type,
Law 2). **The classifier is NOT the session type.** `study-choreography` *refutes* the
seductive "linearity captures I-confluence": linear ⇏ I-confluent (two pool
withdrawals are each linear, jointly not I-confluent — BEC's own counterexample);
I-confluent ⇏ linear (a monotone counter). The classifier is a **BEC invariant-
confluence analysis over the step's `write-set × cell-state-lattice`**, and
CryptoConcurrency shows enforcing the coupled invariant **reduces from consensus** — a
distributed-agreement obligation, categorically not a typing one. No paper in the
corpus marries these three; this is **dregg2's strongest original claim**, and claims
about ZK-conformance and the coalgebraic embedding are downstream of getting this split
right. Everything in the deferred coordination module rests on it.

**Soundness trap if mis-built:** a coupled `Σ=0` settlement is linear and would be
wrongly waved through as "free cross-group" if linearity were trusted to detect
coupling. The three judgements must be carried *separately* per turn.

---

## #2 — Cross-disjoint-group atomic commit is BLOCKING under partition `[IMPOSSIBLE]`

A JointTurn straddling **disjoint reference-groups** needs the commit/abort decision to
reach all groups, but dregg2 has **no single write-point** (no global ledger). **Safety
is provable** (the shared aggregate proof + the CG-5 binding); **liveness is not** —
this is the classic distributed-atomic-commit blocking problem (2PC blocks under
partition; 3PC/Paxos-commit need a shared quorum disjoint groups *don't have*).
**Atomic-cross-group ∧ partition-tolerant ∧ live is impossible.**

This is a **genuine impossibility, not a design oversight** — Mina sidesteps it only by
*being* the one global ledger (`study-mina-relink §5`, `study-consensus §2`). The only
escapes: (a) a shared higher coordinator both groups trust (re-introduces a mediator —
fine *inside* a vat, not across); (b) restrict cross-group turns to I-confluent ops
(#1); (c) accept blocking + timeout-abort for the rare straddling-partition turn. The
concrete gap in code: `ReferenceGroup`/`τ_unified` run per-group; `cross_reference.rs`
*references* a peer group's blocks but cannot make it *agree* on the joint order — a
cross-group turn must form the join-group `G_A ∪ G_B` as one quorum, and **dregg2
specifies no protocol to form it.** This bounds what emergent cross-group coordination
can promise.

---

## #3 — Atomic N-ary choreography steps `[OPEN]`

Standard MPST and choreographies sequence **binary** interactions `p → q : T` (one
sender, one receiver per action); even "multiparty" means *many roles in a protocol*,
**not one atomic synchronous N-way rendezvous as a single step**. A dregg2 step is a
Mina-forest-shaped **atomic N-cell JointTurn** — an equalizer/synchronous N-ary
interaction committing all-or-none (the cumulative-AND prophecy). Encoding an N-ary
atomic step as a *primitive* in a choreography (rather than desugaring to a sequence of
binary sends) **is not standard MPST and is not in the corpus** (`study-choreography`
claim 4, CONFIRMED OPEN). Combined with #2, an atomic synchronous N-ary *cross-group*
step is a real extension of the choreographic model.

---

## #4 — ZK / private choreographies `[OPEN]`

In MPST the global type `G` is **public**. dregg2 wants graph-privacy: a party
ZK-proves conformance to its projection `G ↾ p` **without revealing `G` or others'
moves**. The ZK substrate exists in the corpus (`kachina-private-contracts`,
`uc-zk-smart-contracts`, the Zcash commitment/nullifier pattern) and MPST exists
(externally) — but **their composition does not** (`study-choreography` claim 6,
CONFIRMED OPEN). This is the cleanest fit for the graph-privacy tier: the choreography
structure itself is the thing hidden, proven via the cell's in-circuit admissibility
predicate. dregg2's JointTurn graph-hides the forest topology Mina publishes.

---

## #5 — The IVC impossibility bound `[IMPOSSIBLE]`

There is **no unconditional / arbitrary-depth / NP-witness IVC** (Valiant's conjecture
line; `valiant-conjecture-ivc-impossibility`, `ivc-for-np-standard-assumptions`,
`ivc-arbitrary-depth`). Consequence: **depth is a security parameter; a named
assumption is required** (`decisions §0.2`). Recursion is therefore a *deferrable
feature*, NOT on the soundness-critical path — and the **strand-head-from-genesis
caveat** holds: you cannot get an unconditional succinct proof of arbitrary-depth
history. This is *why* the roadmap puts step-completeness first and recursion behind
the `RecursionBackend` trait (Phase 7). Do not promise unbounded recursion as if it
were free.

---

## #6 — The badge means permitted + effects-as-committed, NOT de-facto authority `[IMPOSSIBLE / seam]`

The load-bearing honesty constraint, and the bound on the zkRPC product. A returned
badge attests **(permitted) ∧ (effects-as-committed)** — a legal CDT derivation existed
(de-jure) and the committed `Obs`-delta + per-class conservation hold (the value rib).
It does **NOT** attest *de-facto authority* — what a holder can eventually *cause* is
recovered behaviorally **from the log, never from the badge** (Miller's `BA`-vs-`TP`
split, `dregg2 §0/§6b`). **Permission survives the crossing; authority does not.** This
is the truth-is-the-log seam: a badge is a value-bearing transition-attestation, **not**
a grant of standing. A zkRPC product that sells the badge as "this principal can do X"
overclaims; it can only sell "this transition was permitted and committed."

---

## #7 — I-confluence is an independent third judgement `[OPEN — see #1]`

Stated separately because it is the recurring trap: **no type captures I-confluence.**
It is a property of the `(transaction-set × invariant)` pair, not of a single process's
channel usage. The closest a *type* gets is the BEC-derived lattice side-condition
(`discoveries §3.7`): a cell may sit at tier-1 *iff* its state is a bounded
join-semilattice with invariant-preserving joins (`I(x) ∧ I(y) ⇒ I(x ⊔ y)`). dregg2
carries **three separate judgements** per turn — conservation (linear), ordering
(session), I-confluence (invariant-merge). **The one live soundness risk
(`study-consensus §5`):** the I-confluence side-condition is documented but **not
type-checked in code** — nothing currently stops a developer declaring a `balance≥0`
cell at tier-1, which *would violate BEC Thm 3.1* (a partition-tolerant, never-blocking
cell preserving a non-I-confluent invariant — the impossible object). The fix is to
make `FinalityRule::admits` a real static check at cell creation.

---

## Adjacent honest residuals (smaller, but do not paper over)

- **Distributed cycle GC is out of scope** `[IMPOSSIBLE-in-practice]`. Refcount-only;
  cross-vat cycles leak, reclaimed by **lease expiry**, never reachability. Cooperative
  distributed cycle-collection is rejected: it needs mutually-distrustful vats to
  truthfully report back-edges (unenforceable) and it leaks the reference graph the
  graph-privacy tier exists to hide (`study-gc §1`). "Dead" is not co-witnessable
  globally; death is *timed out*, never decided.
- **Graph-privacy limit:** a one-time identity still leaks *that* a turn happened at
  time T; full unobservability needs mixing/PIR — out of scope
  (`dregg2-multicell-privacy §7.3`).
- **Schema-DAG fork/merge migration is open.** Linear-chain transparency
  (lazily-migrated ≡ fresh) is proven; the fork/merge case is not (`dregg2 §5`).
- **Revocation's recency floor under partition** `[IMPOSSIBLE]`. Non-membership against
  a stale root accepts a since-revoked credential; you cannot prove a negative about
  unseen events. Root-epoch agreement is weaker than full consensus but **not free** —
  prefer short expiry + renewal (`study-consensus §4`).

---

## Papers to FETCH (corpus gaps) `[GAP]`

The library has **zero** MPST and **zero** choreography papers — every §6 coordination
claim leaning on "projection / global type / choreography" is currently ungrounded in
our corpus (`study-choreography`, "the single most important finding for §6's
reliability"). Fetch before any coordination-layer claim is trustworthy:

1. **Honda, Yoshida, Carbone — *Multiparty Asynchronous Session Types*, JACM 2016** —
   the MPST foundation (cited, absent). *Mandatory before any projection/global-type
   claim.*
2. **Scalas, Yoshida — *Less is More* (POPL'19)** — MPST via CFSMs, full-merge /
   model-checking completeness (claims #2, #3 — projection completeness).
3. **Montesi — *Choreographic Programming* (thesis / *Introduction to Choreographies*,
   CUP 2023)** — the choreography-as-program model + Endpoint Projection theorem
   (claims #3, #4).
4. **A crash / fault-tolerant choreography paper** (Montesi et al. on choreographies
   with failures / fault-tolerant EPP) — directly tests #1's Byzantine-soundness
   novelty.

For the PL comparison (situate dregg2 against the cap/resource/distributed-language
landscape):

5. **Spritely OCapN / Goblins** — the live-cap / vat / distributed-object precedent
   (some material already in `pdfs/{captp,ocapn}-…-spritely.pdf`; fetch the Goblins
   programming model).
6. **The Move resource model** — linear resources as a language type.
7. **CALM / Bloom** — the consistency-as-logical-monotonicity line (the I-confluence
   neighbor #1/#7 needs to be situated against).
8. **Unison** — content-addressed code (the AIR-id / content-addressed `CellProgram`
   precedent).

*(Nice-to-have: a coalgebraic / communicating-automata session-type semantics paper to
make the `G ↾ p ↪ CellProgram` embedding of `study-choreography` claim 3 precise —
`coalgebraic-semantics-silva.pdf` gives the `νF`/bisimulation half but says nothing
about session types.)*
