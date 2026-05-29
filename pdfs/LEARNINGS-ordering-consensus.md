# LEARNINGS — Ordering / consensus (Law 2) & the liquid substrate

> Axis: ORDERING (which arrows compose into which strand = canonicity = consensus), chosen
> per-cell on a pluggable-finality MENU over ONE shared blocklace DAG. Grounded in the seven
> PDFs below + `docs/rebuild/00-synthesis.md §4` (the finality menu) and §2.3 (liquid-first).
> Tags: **[G]** = grounded in a paper/code; **[F]** = forward design / my proposal.

## Papers read

1. **Byzantine Eventual Consistency** (Kleppmann & Howard, 2020.00472) — BEC consistency model;
   the I-confluence iff theorem; Byzantine causal broadcast (hash-DAG + reconciliation).
2. **CryptoConcurrency** (Tonkikh, Ponomarev, Kuznetsov, Pignolet, 2212.04895) — (almost)
   consensusless asset transfer with *shared* accounts; balance-based dynamic conflict detection;
   per-account consensus on demand.
3. **Merkle-CRDTs** (Sanjuán, Pöyhtäri, Teixeira, Psaras, 2004.00107) — Merkle-DAG as a logical
   clock; proves a Merkle-Clock DAG *is* a G-Set CvRDT; CRDT payloads over it; sync = DAG diff.
4. **Mysticeti** (uncertified DAGs, 2310.14821) — implicit certificates by DAG interpretation;
   every-block-committable rule; FPC fast-path = reliable broadcast for single-owner state.
5. **Narwhal & Tusk** (2105.11827) — separate reliable *dissemination* (mempool DAG) from
   *ordering* (consensus); consensus orders only small digests; mempool gives a partial order.
6. **Local-First Software** (Kleppmann et al.) — the seven ideals; CRDTs as the liquid-default
   substrate; "the network is optional."
7. **A Comprehensive Study of CvRDTs/CmRDTs** (Shapiro et al., RR-7506) — the CRDT design space;
   state-based (join-semilattice) vs op-based; SEC. *(Read via its faithful summary embedded in
   the Merkle-CRDT and BEC papers, which cite and restate its core definitions; §2.1 of BEC and
   §II-D of Merkle-CRDT reproduce the join-semilattice/commutativity conditions verbatim.)*

---

## Key ideas (attributed)

### BEC — the sharp impossibility/possibility line **[G]**
- **BEC** strengthens Strong Eventual Consistency with: atomicity, **causal consistency**,
  authenticity, and **invariant preservation**, holding even with an *arbitrary* number of
  Byzantine replicas (Sybil-immune), provided correct replicas form one connected component
  (no eclipse). It does **not** provide total order or serializability — only read-committed.
- **Main theorem (3.1):** a fault-tolerant algorithm ensuring BEC (preserving all invariants)
  exists **iff every pair of concurrently-executable transactions is I-confluent w.r.t. every
  invariant.** I-confluence: if `I(S) ∧ I(S+uᵢ) ∧ I(S+uⱼ)` then `I(S+uᵢ+uⱼ)` for concurrent
  `Tᵢ‖Tⱼ`. Equivalently: concurrent updates must **commute** *and* their merge must preserve `I`.
- **The impossibility proof is brutally simple and worth internalizing:** put the two conflicting
  transactions on the only two correct replicas `p,q`; make every *other* replica Byzantine and
  silent; asynchrony lets `p,q`'s messages be delayed arbitrarily. Fault-tolerance forces each to
  commit without hearing the other; the Byzantine majority refuses to relay the conflict. When the
  partition heals, eventual-update forces both updates to merge into `S+uᵢ+uⱼ`, which violates `I`.
  **No algorithm can escape this** — it is information-theoretic, not a protocol weakness.
- **Examples (Table 1 / §3.3):** non-negative balance is **NOT** I-confluent for *debits from the
  same payer* (two valid withdrawals sum to overdraft) → a currency *cannot* be Sybil-immune →
  needs PoW/permissioned/consensus. Uniqueness constraints are **NOT** I-confluent (two inserts of
  same key) — *unless* the key is `H(message)` (then collision-resistance makes them safe). Credits
  (increases) **ARE** I-confluent. Foreign-key deletes are unsafe; materialized views are safe.
- **Their BEC algorithm IS a blocklace** (§5.1–5.2): messages `(v, hs, sig)` where `hs` = set of
  hashes of causal predecessors; the predecessor graph is a hash-DAG, acyclic by collision-
  resistance; `heads(M)` = no-successor hashes; **union-merge `Mₚ ∪ Mᵣ`** via head-reconciliation
  (Bloom-filter optimized, ~1.03 round trips). Safety check at *delivery* time (`Algorithm 3`):
  a correct replica **discards** any delivered update that is unsafe w.r.t. an invariant — so a
  Byzantine replica's unsafe update simply never enters correct state. **Safety is a function of
  the update + invariant alone, not of current state** (so it can be checked locally on delivery).

### CryptoConcurrency — *when* consensus is avoidable, precisely **[G]**
- Confirms the BEC line from the consensus side: asset transfer with **single-owner** accounts is
  consensus-free (commutative); with **shared** accounts it provably needs consensus *in the worst
  case* (reduction from consensus, ref [24]). The contribution: make consensus **dynamic and rare**
  — invoke it only on an *actual* **overspending attempt**, not on every potential conflict.
- **Key structural insight (§4):** "as long as the final balance of each account is non-negative,
  the resulting state does not depend on the order in which transactions are applied." So the
  *order doesn't matter until the conservation invariant is at risk of violation* — i.e. the
  account is **over-committed** (`TotalValue(active debits) > balance`). Below that threshold,
  parallel/asynchronous; at/above it, fall back to per-account consensus to pick winners.
- **Three transactions, pairwise-OK-but-not-jointly** (the Fig-4 example: 3 spends of 1 on a
  balance-2 account) shows conflict is **not pairwise** — it's a *coverage* property over the
  whole concurrent set. A naive pairwise/1-RTT detector is fooled by one Byzantine replica
  acknowledging all three. They fix it with a Lattice-Agreement-style **Prepare** phase (retry
  until a quorum converges on an identical debit set) + an **Accept** phase (recoverability).
- **Per-account, owner-chosen consensus (§3.3):** "each account uses its own consensus
  implementation, which only the owners of this account trust" — *"if shared by two people, they
  could resolve a conflict via a phone call."* **This is exactly dregg's per-cell pluggable
  finality menu, independently arrived at.** No universal global consensus object.
- Layering: a **Global Storage** (append-only set, not a sequence — "this ledger is not a
  sequence, but just a set") of committed txs + per-account **COD** (overspending detector) +
  per-account **Consensus[acc]** invoked only on recovery. Order is added *locally, on demand*.

### Merkle-CRDTs — the blocklace shape, named **[G]**
- A **Merkle-Clock** is a Merkle-DAG where each node = an event carrying CIDs of its causal
  parents; new events become new roots referencing prior heads. **Theorem (§IV-B): the set of
  Merkle-Clock DAGs forms a join-semilattice `⟨J, ⊆⟩` whose LUB is *set union* `M ⊔ N = M ∪ N`,
  i.e. a Merkle-Clock DAG IS a Grow-Only-Set (G-Set) state-based CvRDT.** Inclusion `Mα < Mβ`
  iff `α ∈ Mβ` (one head reachable from the other); disjoint ⇒ keep both roots (= concurrency).
- A **Merkle-CRDT** = a Merkle-Clock whose nodes additionally carry a CRDT payload `(α, P, C)`.
  The DAG supplies **per-object causal consistency and gap detection for free**: because a node
  names its parents by hash, a replica *cannot apply a node before its predecessors* (the missing
  hashes are detectable and fetchable). This is the key teaching: **the hash-DAG turns an
  unreliable transport into an exactly-once, causal, ordered, verified delivery layer** — so it
  carries even *op-based* CRDTs (which normally demand a reliable causal-delivery messaging layer)
  with zero extra metadata. Sync = DAG-diff from the heads (pull missing sub-DAGs; dedup by CID;
  corrupt nodes self-detect via CID mismatch).
- **Limits (§VI):** ever-growing DAG (can't GC without knowing the full replica set / an external
  truth source); deep-and-thin DAGs make cold-sync slow; merge cost grows with divergence. Total
  order is **not** provided — they note it "could be obtained... by sorting concurrent events by
  CID or any user-defined strategy" = "**data-layer conflict resolution**" (their phrase for what
  dregg calls tier-2+ finality on top of tier-1).

### Mysticeti — uncertified DAG validates tier-1, and the fast-path = single-owner reliable bcast **[G]**
- **Implicit certificates:** instead of each block carrying an explicit quorum-cert (Narwhal's
  `c(d)`), a block is *certified by the DAG structure itself* — if `2f+1` round-`r+1` blocks
  reference (support) block `B`, then any later block whose history contains that pattern *is* a
  certificate for `B`. Equivocation is tolerated: at most one of `A`'s equivocating blocks can
  gather `2f+1` support, and only **implicitly-certified** blocks are ever committed. This removes
  a whole round of signature/cert traffic — "every single block can be directly committed."
- **Mysticeti-FPC fast path** generalizes the uncertified DAG to **transactions that only touch
  state controlled by a single party** — these need only **reliable broadcast within an epoch**,
  *not consensus* (à la FastPay/Zef/Astro/Sui-Lutris). **This is the precise architectural echo of
  the BEC/CryptoConcurrency line: single-owner ⇒ no consensus; shared/contended ⇒ consensus** — and
  it lives on the *same* DAG as the consensus path (no separate certified-DAG black box). It also
  handles cross-epoch recovery of equivocated objects "without losing safety at epoch boundaries."
- n = 3f+1, partial synchrony, liveness only after GST via timeouts; safety always.

### Narwhal — one DAG, pluggable ordering on top **[G]**
- **The thesis dregg needs:** *separate reliable dissemination (mempool) from ordering (consensus).*
  Narwhal is a round-based DAG mempool exposing a key-value block store with **Integrity**,
  **Block-Availability**, **Containment**, **2/3-Causality**, **1/2-Chain-Quality**, and a
  **partial order** on blocks. Consensus (HotStuff *or* the async Tusk) then orders only *small
  digests*; "once we agree on a block digest... we can safely totally order all its causally
  ordered blocks." Throughput becomes independent of the consensus protocol chosen.
- The DAG provides a partial order **always** (even under full asynchrony); total order is a
  *pluggable layer* (Narwhal-HS = partial-sync; Tusk = async). **This is "one DAG, pluggable
  finality on top" in the literature, verbatim in spirit.**

### Local-First — the liquid-default philosophy **[G]**
- Seven ideals: (1) no spinners / instant local response, (2) work across many devices, (3) **the
  network is optional** (offline-first), (4) seamless real-time collaboration, (5) **the Long Now**
  (longevity — data outlives any vendor), (6) **security & privacy by default**, (7) you retain
  **ultimate ownership & control**. CRDTs are presented as the substrate that delivers (1)(3)(4)
  *while being fundamentally local and private* — exactly synthesis §2.3's "liquid by default."
- Notably scopes itself OUT of "banking / e-commerce / social / ride-sharing... well served by
  centralized systems" — an honest admission that maps to the BEC line: the *I-confluent* apps are
  the local-first sweet spot; the non-I-confluent ones (money) want a stronger tier.

---

## Takeaways for dregg (idea → move; map to synthesis §/code)

1. **[G→F] Tier-1's safe set is *exactly* the I-confluent transactions.** synthesis §4 says tier-1
   "never blocks." BEC Thm 3.1 tells us the *price*: tier-1 can only preserve invariants that are
   I-confluent w.r.t. the cell's transactions. → **Make I-confluence a typed, checkable property of
   a cell's action set, and let it *gate* whether a cell may run at tier 1.** A cell whose
   invariants are all I-confluent is provably tier-1-safe against arbitrary Byzantine load; a cell
   with a non-I-confluent invariant (e.g. `balance≥0` under debits) *must* escalate to tier-2+ for
   the contended operations. This turns the finality menu from a free dial into a **soundness-typed
   dial** (cf. synthesis §5.3 "promote finality to config" — but now config is *constrained by the
   invariant lattice*).

2. **[G] The blocklace IS a Byzantine-causal-broadcast hash-DAG + a Merkle-Clock G-Set.** The
   substrate (`blocklace/finality.rs` = per-creator chains + CRDT union-merge; `ReferenceGroup` =
   a DAG view) is *literally* the BEC `M` set and the Merkle-CRDT DAG. → **Adopt BEC's
   delivery-time safety check** (synthesis §5.2 "sets→cells"): a correct cell, on *applying* a
   delivered block, re-checks the per-invariant safety predicate and **discards** unsafe blocks —
   so Byzantine equivocation "harms only a finite prefix" becomes "harms nothing in correct state."
   This is the missing teeth on the union-merge: union is monotone, but **application must filter**.

3. **[G→F] CryptoConcurrency = the reference design for tier-1↔tier-3 *crystallization*.** Its
   "consensus only on an actual overspending attempt" is exactly synthesis §4's "a block written
   under tier 1 can be finalized under tier 3 later if a group decides to order it." → **Model the
   escalation trigger as `TotalValue(active debits) > balance`** (a conservation-margin predicate),
   not as a static "this op type is red." Below margin → stay liquid (tier 1); at/over margin →
   the cell's *owner-chosen* `Consensus[cell]` instance picks winners and writes a snapshot
   (their COD `Close`+recovery = dregg's crystallization checkpoint). Maps to §4 "`C` selects the
   finality rule" and §1's Law-1 Conservation *constraining* (not deciding) the search.

4. **[G] Per-cell, owner-chosen consensus is sound and is in the literature.** CryptoConcurrency
   §3.3 ("each account uses its own consensus; trusted only by its owners") + Narwhal's
   pluggable-ordering-over-one-DAG + Mysticeti-FPC's single-owner-fast-path together **validate the
   per-cell finality menu and its 4 tiers as a recognized design point, not an invention.** →
   keep §4 as-is; cite these three as grounding. Lift `½(n+f)` into per-group config (§4 todo).

5. **[G] Single-owner ⇒ no consensus is a *theorem-backed* default, not an optimization.** BEC
   (commutative single-writer increments are I-confluent), CryptoConcurrency (single-owner accounts
   are consensus-free), Mysticeti-FPC (single-party state = reliable broadcast only) all agree. →
   **A solo-owned cell (the n=1 default, synthesis §4 tier-1) is provably the maximal liquid case**;
   the regression synthesis §0 names ("built solid-first") is recoverable precisely because the
   single-owner-fast-path is theoretically free.

6. **[G→F] Use `H(block)`-derived keys to make uniqueness I-confluent.** BEC Table 1: a uniqueness
   constraint is unsafe under user-chosen keys but **safe if the value is `H(message)`.** dregg's
   nullifier/revocation **sets-as-cells** (synthesis §5.2) already key by hash. → This is *why*
   they're tier-1-safe: a nullifier set is a **G-Set keyed by content hash** = the canonical
   I-confluent CvRDT. Document this as the soundness reason, not just a convenience.

---

## Fundamental limits (what tier-1 can never guarantee; when consensus is avoidable)

**[G — these are theorems, state them precisely]**

- **Tier-1 (causal-only CRDT) can NEVER guarantee a non-I-confluent invariant against concurrency.**
  Concretely it can never, by itself, enforce: `balance ≥ 0` under concurrent *debits* from the
  same payer (double-spend / overdraft); global *uniqueness* of a user-chosen key; *exactly-once*
  effects across replicas for a non-idempotent op; any "at most k of these may succeed" cap;
  referential integrity under concurrent delete+insert. (BEC §2.2, §3.3, Table 1.)
- **It CAN guarantee** (at tier 1, Sybil-proof): grow-only sets/counters, monotone *increases*
  to a value, content-hash-keyed uniqueness, last-writer-wins registers, observed-remove sets with
  causal tombstones, materialized views — i.e. any invariant that is **I-confluent** = the merged
  state preserves it whenever each branch did. The lattice condition (below) is the test.
- **The avoidability rule (from both BEC and CryptoConcurrency):** consensus (tier ≥ 2/3) is
  needed **exactly when** concurrent operations on a cell are *not* I-confluent AND they are
  *actually in contention* (the conservation/coverage margin is exceeded). Two refinements:
  - **Static avoidability:** if a cell's whole action set is I-confluent, consensus is *never*
    needed (tier-1 forever). (BEC.)
  - **Dynamic avoidability (the better one):** even for a non-I-confluent invariant like
    `balance≥0`, consensus is needed *only in executions where the concurrent set would actually
    overspend*; conflict-free-but-concurrent executions stay tier-1. (CryptoConcurrency Thm 1 /
    Transfer Concurrency property — `k+4` RTT fast path, consensus only on overspend.)
- **Hard floor on the consensus tiers** (CryptoConcurrency intro, BEC §1): BFT consensus needs
  `n ≥ 3f+1`, partial synchrony (or randomization) for liveness, `Ω(f²)` messages / `Ω(f)` rounds.
  So tier-3/4 **stall on partition** (no GST ⇒ no progress) — synthesis §4's table is correct.
  Tier-1/2 **never block** but cannot decide non-I-confluent conflicts. *There is no tier that does
  both* — this is the CAP-shaped wall the menu is honestly built around, not a gap to be closed.
- **Connectivity caveat [G]:** even tier-1 needs correct replicas in **one connected component**
  (no eclipse). "Phones over Bluetooth keep working" (§4) holds only while the honest set isn't
  partitioned *through only Byzantine relays*. Worth a footnote in §4's tier-1 row.

---

## Tensions & corrections

- **[correction] synthesis §4 says the blocklace tolerates "Byzantine equivocation harms only a
  finite prefix."** BEC is more precise and stronger: with the **delivery-time safety filter +
  hash-DAG causal completeness**, equivocation by a Byzantine creator harms *nothing* in correct
  state — the conflicting block is either never delivered (missing predecessors) or discarded
  (unsafe), and vector-clock-style corruption (BEC Fig 4) is avoided because **heads are hashes,
  not counters.** → Recommend §4 say "equivocation cannot corrupt correct-replica state; it can at
  most withhold," and note the blocklace must **not** use vector clocks for head summaries (a real
  pitfall: BEC §4.2 shows a Byzantine node can forge equal vector timestamps over different sets).
  *Check `blocklace/finality.rs` does head-reconciliation by hash, not by per-creator counters.*
- **[tension] "tier-1 never blocks" vs. invariant preservation.** It's true tier-1 never *blocks*,
  but to preserve a non-I-confluent invariant it must **reject** (drop) concurrent unsafe updates —
  which from the *user's* view looks like a silently-failed transaction (CryptoConcurrency's
  account-blocking pathology in naive consensus-free systems). The honest framing: tier-1 trades
  *blocking* for *unilateral rejection of one side of a conflict*; recovering the rejected side is
  what tier-2+/COD-recovery is for. The menu should surface this as a per-cell policy, not hide it.
- **[tension] Merkle-CRDT ever-growing DAG + no-GC-without-known-replica-set** vs. dregg's
  "n=1 grows, no genesis ceremony / dynamic membership" (§4). You **cannot** safely prune the
  blocklace at tier-1 (open membership) without an external truth source. → GC/compaction is itself
  a **tier-bound operation**: only a tier-3 group with known Π can truncate stable prefixes (BEC
  §5.4 "once `m` is stable... predecessors can be removed"). Pruning is a *crystallization side
  effect*, not a tier-1 capability. **[F]**
- **[tension] off-diagonal regime corners (synthesis §9 decision 2).** A "proof-carrying cell that
  still wants single-writer ordering" is fine (proof ⊥ ordering). But a cell that wants *both*
  tier-1 liveness *and* a non-I-confluent invariant is **forbidden by BEC** — that corner is not
  "allowed but the membrane handles it," it's *unrealizable*. The 4-corners model must mark this
  corner as a **type error**, not a membrane responsibility.
- **[nuance] conflict is not pairwise.** CryptoConcurrency Fig-4 kills the intuition that "detect
  pairwise conflicts" suffices — `k` operations can be pairwise-safe but jointly overspend.
  Any dregg escalation trigger must be a **coverage/sum predicate over the whole concurrent set**,
  verified against a quorum-converged set, not a pairwise check. (Affects intent `RingSolver` and
  any tier-2 ack-threshold detector — synthesis §3.2's bounded matcher.)

---

## Proposed artifacts **[F unless noted]**

### A. The finality-tier interface (refines synthesis §4 `C`)
```
trait FinalityRule {
    // Liveness/safety class — what the rule promises.
    fn tier(&self) -> Tier;                 // 1 Causal | 2 AckThreshold | 3 TauBFT | 4 Constitutional
    fn membership(&self) -> Membership;     // Open(n≥1) | KnownSet{ n, f } | PKI{ amendable }
    fn never_blocks(&self) -> bool;         // true iff tier ≤ 2 (BEC: causal/ack degrade, don't stall)

    // The soundness gate (BEC Thm 3.1): may this rule carry this cell's invariants?
    //   tier 1 accepts ONLY if every invariant is I-confluent w.r.t. the action set.
    fn admits(&self, inv: &InvariantSet, acts: &ActionSet) -> Result<(), NotIConfluent>;

    // Decide canonicity for a contended slot. tier 1 = ⊥ (no decision; union + filter).
    fn order(&self, dag: &Blocklace, slot: Slot) -> Decision;  // Causal => Unordered{partial}
}
```
- **Tier-1 `admits`** = run the I-confluence check; **tier-1 `order`** = none (return the causal
  partial order; conflicts resolved by delivery-time *filter*, not by ordering).
- **Crystallization** = swapping a cell's `FinalityRule` from a lower to a higher tier and running
  the higher rule's `order` over the already-written DAG slots (CryptoConcurrency COD `Close`→
  `Consensus[acc]`→snapshot is the canonical sequence).

### B. The cell-state lattice requirement (what makes a cell tier-1-safe) **[G-derived]**
A cell may run at tier 1 **iff** its state type is a **bounded join-semilattice** `(S, ⊔, ⊑)` with:
- **⊔ idempotent, commutative, associative** (CvRDT join; Merkle-CRDT §II-D / Shapiro RR-7506);
- **every action is an inflation**: `s ⊑ act(s)` (monotone — no rollback needed on reorder);
- **the join of two valid states is valid**: `I(x) ∧ I(y) ⇒ I(x ⊔ y)` — **this is I-confluence
  re-stated as a lattice closure property**, and it is the load-bearing condition (BEC Thm 3.1).
The canonical tier-1 cells: G-Set (nullifiers, keyed by `H`), G-Counter, OR-Set with causal
tombstones, LWW-Register, Merkle-Clock-of-events. **`balance≥0` fails the third condition** (the
join of two individually-valid post-debit states can be invalid) ⇒ not a tier-1 lattice ⇒ must
escalate on contention. → synthesis §5.2 "sets→cells" cells are exactly the safe ones; this is the
*criterion* for which executor side-tables can become tier-1 cells and which need a finality rule.

### C. The cross-tier composition rule (the membrane for heterogeneous ordering) **[F]**
A single turn touching cells `c₁…cₖ` at tiers `t₁…tₖ` is **ordered at `max tᵢ`**, and the membrane
must enforce:
1. **Monotone-tier rule:** a turn may freely *read* from any tier and *write* to cells of tier
   `≤ its own commit tier`; **writing to a higher-tier cell forces the whole turn up to that tier**
   (you cannot finalize a tier-3 cell with only tier-1 evidence). The turn's effective tier is the
   **join of its written cells' tiers** (a lattice on Tier).
2. **No-downgrade rule:** a value that has been finalized at tier `t` cannot re-enter a tier-`<t`
   computation as if liquid — crossing *down* requires re-wrapping it as an immutable input
   (synthesis §2.4 "proof = export format of the log"; CryptoConcurrency's commit-certificate that
   a credit carries into the next COD epoch is exactly this).
3. **Conservation is tier-independent (Law 1 ⊥ Law 2):** the linear/conservation check
   (synthesis §1, `LinearityClass`) runs identically at every tier — it *prunes* the order search
   (CryptoConcurrency: "balance non-negative ⇒ order doesn't matter") but never *decides* it. So a
   multi-tier turn first checks conservation (cheap, any tier), then orders only the
   non-I-confluent / contended portion at the join tier.
4. **Atomicity across tiers [G-anchored]:** BEC's *Atomicity* property (apply all updates of one
   transaction together) means a cross-tier turn's tier-1 writes must not become visible until the
   join-tier portion finalizes — realized by synthesis §1's "outgoing effects held until commit"
   (Spritely). The membrane = the held-effects boundary, parameterized by the join tier.

**Soundness claim [F, but each clause is paper-anchored]:** a heterogeneous turn is sound iff it
commits at the join of its written-cells' tiers, its conservation check passes at that tier, and
no finalized value is downgraded. The unsound corner (tier-1 liveness + non-I-confluent write) is
*statically rejected* by artifact-A's `admits`, not handled at runtime.

---

## Open questions / what to read next

1. **Is `blocklace/finality.rs` head-summarization hash-based (safe) or counter/vector-based
   (BEC §4.2 vulnerable)?** Must verify — this is a concrete soundness bug if vector-clock-style.
2. **Does dregg apply BEC's delivery-time invariant *filter*, or only union-merge?** If only union,
   the "equivocation harms only a finite prefix" claim is too weak; need the discard-on-unsafe step.
3. **Tier-2 (ack-threshold) formal placement:** BEC has no tier-2 — it's tier-1 (causal) or full
   BFT. Is ack-threshold a *safety* mechanism or just a latency hint? CryptoConcurrency's Prepare
   phase (quorum-converged debit set) is the closest analog — read its Appendix A (COD pseudocode)
   to ground tier-2 precisely. **Likely tier-2 = "I-confluent fast path with a recoverable detector,
   no leader" — i.e. CryptoConcurrency's COD without the consensus fallback wired in.**
2'. **DAG-Rider / Bullshark commit rules** (Mysticeti & Narwhal both build on them) — read for the
    exact tier-3 `order` implementation dregg's `τ_unified` should expose.
4. **GC/compaction as a tiered operation:** confirm dregg never prunes at open membership; design
   the tier-3 stable-prefix truncation (BEC §5.4) as the only safe pruning path.
5. **Generalized Lattice Agreement** (Falerio et al., cited by CryptoConcurrency) — the formal
   abstraction underneath both COD and tier-2; likely the right primitive for the `FinalityRule`
   trait's tier-2 `order`. Worth reading directly.
6. **Read the full Shapiro RR-7506** (only read via secondary summaries here) to lock the exact
   CvRDT/CmRDT taxonomy for artifact-B and confirm the OR-Set / PN-Counter lattice proofs dregg's
   non-nullifier cells will need.
