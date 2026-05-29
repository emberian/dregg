# STUDY-cyclic-gc — Can dregg2 beat lease-expiry for cyclic GC?

> **Question (from `discoveries-2 §1`).** dregg2 ships ACYCLIC distributed GC
> (refcount-at-zero on the append-only CDT) + **lease-expiry for cycles**, and flags
> cyclic collection on the *live-reachability* graph (A→B, B→A keeping every
> refcount ≥1) as genuinely open. Pony's **ORCA** collects cyclic garbage
> concurrently without stop-the-world and has a machine-checked soundness proof
> (ESOP'18). Can ORCA's mechanism do better than lease-expiry-only for dregg2 —
> *under Byzantine, partitioned peers*?
>
> **Sources.** `orca-actor-gc-type-codesign-oopsla17.pdf` (mechanism),
> `orca-soundness-concurrent-actor-gc-esop18.pdf` (soundness/assumptions),
> `dregg2.md §1.7/§10`, `study-gc.md`, `captp/src/gc.rs`, `cell/src/capability.rs`,
> `metatheory/Metatheory/Boundary.lean`. Tags: `[G]` paper · `[C]` code (`file:line`)
> · `[F]` forward-design · `[!]` hard limit.

---

## 0. Verdict (decisive)

**dregg2 can do strictly better than lease-expiry-*only*, but ORCA's headline result
does not transfer — and the part that does transfer is the part dregg2 *already has*.**
The honest decomposition:

- **ORCA's "object cycles need no special treatment" is NOT cycle collection.** It is
  *single-owner* refcounting where the deferred count is "actor interest," not
  topology. It collects *object* cycles only because **every object has exactly one
  owning actor that traces its own heap locally** `[G]` (`orca17:920-929`). The
  genuinely-cyclic case — a cycle of **actors** (the dregg2 analog: a cycle of
  *cells/vats* with no owner above them) — ORCA explicitly **delegates to a separate
  protocol, MAC (Clebsch–Drossopoulou 2013), and disclaims it** (`orca17:215, :488`,
  footnote 2: *"Cycles of actors are handled separately from Orca"*). dregg2's open
  problem (A@vat1 ↔ B@vat2, no root) is precisely the **actor-cycle** case ORCA
  punts. `[G][!]`
- **What transfers: the single-owner discipline itself.** ORCA's whole soundness rests
  on *ownership* — one actor authoritatively counts each object and may collect it on
  purely local information (`orca18` Lemma 2: `LRC=0 ∧ no local path ⇒ globally
  inaccessible`). dregg2's exporter-owns-the-export model (`ExportGcManager`,
  `gc.rs`) is **the same discipline already** — and is why a false `DropRef` is
  self-harm, not cross-harm (`study-gc §2`). So the ORCA mechanism is largely *the
  refcount half dregg2 ships*, recognized.
- **What does NOT transfer (the Byzantine delta): every ORCA assumption is a
  cooperative/crash-free/shared-machine assumption that a mutually-distrustful net
  voids.** Causal delivery, FIFO per-actor queues, honest INC/DEC, and (for actor
  cycles) MAC's confirmation rounds all require peers that *answer truthfully and
  eventually*. A Byzantine peer breaks confirmation by refusing, lying, or
  partitioning — and the failure mode of MAC-style confirmation under a liar is
  **premature collection (a safety break)**, which is categorically worse than
  lease-expiry's failure mode (a bounded leak).
- **Therefore the recommendation is a HYBRID:** run ORCA/MAC-style **cooperative
  cycle-collection only inside a cooperative quorum (one trust-root, or a
  consensus-group that already agrees on a finality tier)**, and keep **lease-expiry
  as the sole mechanism across Byzantine strand boundaries**. The improvement over
  today is real but **scoped to the cooperative interior**; across distrust, the
  lease stays, and that is provably necessary, not a punt.

---

## 1. ORCA mechanism — how it actually collects concurrently `[G]`

ORCA is a runtime/type-system **co-design**. Three pieces:

**(a) Ownership + deferred reference counts (the object case).** Every object has one
**owner** actor, fixed for life (`orca18:176`). The owner keeps the authoritative
count `LRC(ω)`; every *other* actor referencing `ω` keeps a *foreign* count `FRC(ω)`.
The counts are **not** the reference topology — they are an **upper bound on the
number of actors (or in-flight messages) with a stake in the object** (`orca17:79-86`,
`:482`). Updates are *deferred* and *piggy-backed* on application messages: sending an
object that you don't own decrements your `FRC` non-atomically; if your `FRC` is too
small you "inflate" it by a constant `GCINC` and send an `acquire`/INC to the owner
(`orca17:633-650`). The owner collects `ω` when `LRC(ω)=0` **and** no local path
reaches it — **purely local information, no global snapshot** (`orca18` Def 10 / Lemma
2). This is why *object* cycles "need no treatment": each owner traces its own heap; a
globally-unreachable cycle spanning n owners gets each owner's decrement when that
owner next GCs, and after all n have run one GC cycle every member has `LRC=0`
(`orca17:920-929`). **No cycle detector runs — single ownership dissolves the cycle
into n independent local refcounts.** `[G]`

**(b) The race-free tracing (the type-system half).** Pony's deny-capability /
reference-capability system (`iso/val/ref/box/tag`) guarantees that if an actor can
*mutate* an object, no other actor can even *read* its fields (`orca18:115-159`). So
the collector can **trace an object without locks, barriers, or stopping the mutator**
— tracing on message send/receive *replaces* write barriers. This is the load-bearing
co-design: GC concurrency is *free* because the type system already excludes data
races.

**(c) The confirmation protocol (the actor case — what dregg2 actually needs).** ORCA
proper does **not** collect actor cycles; the cited MAC protocol does. Its shape (from
the literature ORCA defers to): when an actor *might* be in an unreachable cycle, the
detector sends a wave of messages and **waits for confirmation that no live path
exists** — a deferred, message-counting consensus on "is this cycle dead." It works
because, in ORCA's world, every actor **cooperates and eventually answers**, and
**causal delivery** keeps the confirmation counters consistent.

**What ORCA assumes (the soundness preconditions — `orca18 §2`, Def 14):**
1. **Single owner per entity, ownership fixed for life** (`orca18:176`). `[G]`
2. **Causal message delivery** — every message delivered after its causes
   (`orca18:160-169`). *Crucial for safety:* it forces INC before DEC so the owner
   never sees a decrement-to-zero while a holder still has the ref (`orca17:882-895`,
   the A/B/C example). `[G]`
3. **FIFO per-actor queues + honest, eventual processing** — the well-formed-queue
   invariant I7 (`orca18:1116-1188`) requires that the *effect of any prefix* of an
   actor's queue keeps every live `LRC > 0`. This is a statement about an **honest,
   non-dropping, non-reordering** actor.
4. **Type-system-enforced race freedom** (deny capabilities). `[G]`
5. **Shared trust domain** — all actors run one runtime; no actor lies about its
   counts or forges another's messages.

Soundness (Thm 3, `orca18:1188`): under I1–I8, ORCA **never collects an accessible
object** (safety) and **eventually collects every inaccessible one** (Thm 2,
completeness). Both proofs *consume every assumption above*.

---

## 2. The Byzantine delta — what survives, what forces the lease `[!]`

dregg2's vats are **mutually-distrustful hosts over an untrusted net** (`dregg2 §0`).
Map ORCA's five assumptions onto that setting:

| ORCA assumption | dregg2 reality | Survives? |
|---|---|---|
| Single owner, fixed for life | **Holds** — exporter owns the export edge; `process_drop` only touches `holders[from]` (`gc.rs:183`). | ✅ this is the part that transfers |
| Causal delivery | Holds **only within a CapTP session** (FIFO, `session.rs`); **across the net, no global causal order** — that's exactly what dregg2 *refuses* (§2.2 rejects "single global total order"). | ⚠️ bilateral only |
| FIFO + honest eventual processing (I7) | A Byzantine peer **need not process, answer, or be truthful**. | ❌ |
| Type-enforced race-freedom | Replaced by **crypto** (session/epoch gating, signed caps) — *stronger* against forgery, but says nothing about a peer's *internal* graph. | ⚠️ different guarantee |
| Shared trust domain | **Voided by definition.** | ❌ |

**What a malicious peer can do to a cooperative cycle-collection protocol:**

- **Refuse to confirm / never answer.** A MAC-style confirmation wave **blocks**
  waiting for the cycle's members to report "no live path." A Byzantine member simply
  never replies. Confirmation cannot complete ⇒ the cycle is never collected. This is
  *exactly* the "refuse-to-drop" griefing of `study-gc §2`, lifted to a protocol that
  needs a *quorum of answers*, not a single drop. The protocol's liveness is now
  hostage to the most-uncooperative member. `[!]`
- **Lie about refcounts / back-edges.** Cooperative cycle detection (Bacon–Rajan
  trial-deletion, MAC confirmation) requires peers to **truthfully report their
  internal references into the candidate set**. A peer that *under-reports* (claims it
  dropped a back-edge it still holds) drives the detector to conclude "dead" and
  **collect a still-live cell — a SAFETY violation**, the catastrophic outcome.
  ORCA's own safety leans entirely on I7's honest-queue guarantee; remove honesty and
  Thm 3 has no hypotheses. There is **no local check** that catches a lying
  back-edge-report, because the back-edge lives inside the liar's private heap — which
  dregg2 *deliberately hides* (tier-3 graph privacy, §6a). **Cycle-collection
  cooperation and graph-privacy are in direct tension** (`study-gc §1`, option 3). `[!]`
- **Partition.** Under partition the confirmation wave's replies never arrive;
  indistinguishable from "refuse." dregg2's stance (§2.2 tier-1) is *never block on
  partition* — a confirmation protocol that blocks violates the local-first
  contract outright.

**The asymmetry that decides it.** dregg2's *current* refcount GC fails **safe**: a
lost/forged/withheld `DropRef` causes a **leak, never a premature collection** —
because a drop only decrements the dropper's *own* holder entry and is session/epoch
gated (`gc.rs:183/193`, `byzantine_node_different_session_cannot_drop_others_refs`
test `gc.rs:670`). A cooperative **cycle**-collector fails **unsafe** under a liar:
its whole job is to collect something *no single peer's count says is dead*, so it
*must* trust an aggregate of peer reports, and a false report ⇒ premature collection.
**Moving from refcount to cooperative cycle-collection across a trust boundary trades
a bounded leak for a use-after-free.** That is a strictly worse failure mode, and it is
why **the lease-expiry fallback must remain across every Byzantine boundary**. `[!]`

**What this means for ORCA-transfer:** ORCA's *object* mechanism (single-owner deferred
refcount) transfers and is *already in `gc.rs`*. ORCA's *concurrency* (lock-free
tracing) transfers as a local intra-vat optimization. ORCA's *actor-cycle* collection
(MAC confirmation) **does not transfer across distrust** — its safety hypotheses are
exactly the ones the threat model removes.

---

## 3. Recommendation — a concrete hybrid for dregg2 `[F]`

**Design: trust-scoped cycle collection. Cooperative inside a quorum; leased across
Byzantine strands.**

Partition the reference graph by **trust boundary**, using the unit dregg2 already has:
the **`StrandId`** (the bilateral peer) and its grouping into a **cooperative quorum**
(a set of strands that already share a finality tier ≥2, i.e. that already agreed to
cooperate and answer — §2.2). Then:

**Tier A — intra-vat (one trust-root): full local cycle collection.** `[F]`
A vat can trace its *own* heap and collect cycles wholly inside itself with **zero
protocol** — this is the ORCA-object case where the owner is the only stakeholder, and
needs no peer cooperation, no causal-delivery assumption, no Byzantine concern. **Ship
this.** It is the "local cycle collection only" of `study-gc §1` option 2, and it is
free and provably safe (the owner has complete information). Maps to: a `mark` pass
over the vat-local `CapabilityRef` graph rooted at vat-resident CSpace slots; collect
any strongly-connected component with no root path. `[G→F]` (ORCA Lemma 2 is the
soundness template — *local information suffices when you own everything in the SCC*.)

**Tier B — cooperative quorum (a tier-≥2 group that opted in): ORCA/MAC-style
confirmation, gated on cooperation + accountability.** `[F]`
Across strands *within one finality group* (peers who already run ack-threshold or
τ-BFT, §2.2 tiers 2–4), run a confirmation-based cycle detector. This is safe **only
because** the group has already paid for cooperation: it has a quorum, it has a tier
that *stalls rather than lies* under partition, and — critically — peer reports can be
made **accountable** (signed back-edge attestations bound to the CDT, so a false
report is a *detectable, attributable* equivocation, slashable like any other tier-≥2
fault). The cycle-collect becomes **a turn**: a `JointTurn` (§1.6) over the SCC's
member cells whose proof asserts "every member attests no live root-path into this
SCC," verified as a CG-2 ⊗ CG-5-style cross-cell binding. **Provable:** *if* every
member's attestation is honest (enforced by the group's tier), collection is sound.
**Heuristic / not free:** the honesty is bought by the tier's fault model, not by GC —
so Tier B inherits exactly the group's BFT assumptions and **stalls (does not lie)
under partition**, which is acceptable *because the group already accepted stalling*.

**Tier C — across Byzantine strand boundaries: lease-expiry, unchanged and
load-bearing.** `[C/F]`
Between strands with no shared cooperative quorum, **do not attempt cycle
collection.** Cross-vat cycles are reclaimed by `expires_at` (`capability.rs:56`) +
`stale_exports(max_idle)` (`gc.rs:219`). This is provably the only safe choice (§2:
the alternative is use-after-free under a liar), it is partition-tolerant, and it
already exists. Promote `expires_at` from incidental to **the first-class liveness
bound** (the `study-gc §5` doc-correction).

**Mapping onto `captp/src/gc.rs` + the `StrandId` re-keying:** `[C/F]`
1. **Land `TODO(unified-lace)` first** (`gc.rs:14`): key exports/drops on `StrandId`,
   not `FederationId`. The strand-keyed methods already exist
   (`record_export_by_strand`, `process_drop_by_strand`, `gc.rs:~290-305`) but wrap a
   `StrandId` into a `FederationId([..])` for storage. Make the *table* strand-keyed.
   **Why this gates everything:** Tier B's "is this peer cooperative + accountable" and
   Tier C's "is this a Byzantine boundary" are both **per-strand** questions; the group
   key (`FederationId`) cannot answer them. It is also the one place the current
   Byzantine-safety argument is load-bearing on an unfinished migration — under 3-party
   handoff (`handoff.rs`), an export's holder may differ from its arrival session, so
   drop-attribution can be mis-keyed across the group until this lands (`study-gc §4`).
2. **Add a `trust_class: StrandId → {SelfOwned | Quorum(group) | Byzantine}`** lookup
   (sourced from the finality-tier config, §2.2). It routes a strand's exports to
   Tier A / B / C.
3. **Tier A:** a new local `cycle_collect()` on the vat's own cell graph (entirely
   new, but local-only — no protocol). **Tier B:** a `CycleCollectTurn` =
   `JointTurn` over the SCC, reusing `bilateral_aggregation_air` machinery (§1.6) to
   verify the joint no-root-path attestation. **Tier C:** unchanged `stale_exports`.
4. **Keep the existing session/epoch gating (`gc.rs:193`) as the Byzantine-safety
   floor under all tiers** — even Tier B's attestations are session-bound.

**Net improvement over today:** dregg2 today collects *zero* cycles (refcount-only,
`study-gc §1`). The hybrid collects **all intra-vat cycles (free, provable)** and
**cross-strand cycles within a cooperative group (provable modulo the group's BFT
assumption)**, and falls back to lease only across genuine distrust — where the lease
is provably necessary. That is strictly better than lease-expiry-only, with the
honesty that the improvement is *trust-scoped*, not universal.

---

## 4. Coinductive fit — the `ν` "while reachable" side-condition `[F]`

`Boundary.lean` states soundness as a `▶`-guarded bisimulation over
`Cell = νC. µI. StepProof I × (Turn ⇒ C)` (`dregg2 §1.3/§8`). §1.7 makes reachability
the **well-foundedness side-condition on the outer `ν`**: the unfold proceeds forever
*while reachable*. The hybrid sits cleanly on this — and *sharpens* it:

- **Reachability is a coinductive (greatest-fixpoint) predicate, and that is exactly
  the right shape.** "`c` is live" = "there exists a root-path of un-dropped edges into
  `c`" is **`ν`-flavored: positively semi-decidable by exhibiting an observation (a
  finite live path = a `Verify`)** (`study-gc §3`). Death — "*no* path exists" — is the
  universally-quantified, globally-quantified negation, which is **not finitely
  co-witnessable across distrust + privacy** (`study-gc §3`, `[!]`). The three tiers are
  precisely three *decidable approximations* of this undecidable `ν`-predicate:
  - **Tier A** decides it *exactly* — the owner has the whole SCC, so "no root-path"
    is a finite local check (this is ORCA's Lemma-2 locality recovered coinductively:
    when you own the whole strongly-connected component, the greatest fixpoint is
    computable).
  - **Tier B** decides it *relative to the group's honesty* — the joint attestation is
    a finite witness of `¬reachable` valid *under the tier's fault assumption*. It
    discharges the side-condition as a `JointTurn` hypothesis (the §1.6 CG-2⊗CG-5
    binding), **not** a per-cell theorem — consistent with §10's honesty note that
    cross-cell soundness is an irreducible bilateral *hypothesis*, never derivable from
    single-cell `step`.
  - **Tier C** does **not** decide death — it **times it out**. Lease-expiry converts
    the non-co-witnessable `ν`-predicate "dead" into the locally-decidable "lease
    lapsed" (`study-gc §3`). Categorically: the lease is a **`µ` (least-fixpoint /
    inductive) clock laid over the `ν` codata** — it *forces* termination of an unfold
    that the greatest fixpoint alone would let run forever. This is the **dual** of the
    productivity guard `▶`: `▶` says "you may keep unfolding (later)"; the lease says
    "you must stop unfolding (deadline)." The `ν` carries *both* a productivity guard
    (forward) and a reachability/lease side-condition (the GC backward face, §1.7).
- **The drop = backward-await framing holds for Tiers A/C, strains for B.** A single
  `DropRef` is a fire-and-forget settled-negative advancing the exporter's `Obs`
  (`study-gc §4`) — the clean backward face. Tier B's confirmation wave is **not**
  fire-and-forget: it is a *suspend-and-resume* join over multiple peers (a genuine
  `JointTurn`), so it is the backward face of the **cross-cell ⊗** await, not the
  single-cell one. This is the same "mild strain, structurally honest" extension §10
  already documents for ⊗: the coinductive frame *composes via ⊗* to carry Tier B, but
  Tier B's soundness is the irreducible joint binding, not an inhabitant of one cell's
  `step`.

**Bottom line for `Boundary.lean`:** the side-condition becomes *tiered*:
`Live(c) := SelfReachable(c) ∨ QuorumAttested(¬dead, c) ∨ ¬LeaseLapsed(c)`. The first
is a decidable local predicate, the second a `JointTurn`-discharged hypothesis, the
third an inductive clock. None requires a global snapshot; all three are sound
*approximations from below* of the true `ν`-reachability, which is the only honest
posture given no-global-snapshot + graph-privacy.

---

## 5. Risks & open

- **`[!]` Tier B safety = the group's BFT safety, no more.** A false back-edge
  attestation inside a quorum, if it evades slashing, is a use-after-free. Tier B is
  only as sound as the finality tier it rides on; it must **inherit, never weaken**,
  the group's fault threshold. If unsure a strand is genuinely in a cooperative quorum,
  **default to Tier C** (fail-safe to leak, never to collect).
- **`[!]` Graph-privacy vs. Tier B cooperation (irreducible tension).** Tier B's
  attestations reveal *some* back-edge structure to the quorum — exactly what tier-3
  graph privacy (§6a) hides. A privacy-preserving Tier B needs the attestation to be a
  **ZK proof of `¬root-path` over committed edges** (a `Witnessed{Custom{...}}`
  constraint, like the blinded-queue spend) rather than a cleartext report. Feasible in
  principle (it is the same shape as the ZK auth-chain) but **unbuilt and nontrivial**;
  until it exists, Tier B and graph-privacy are mutually exclusive for a given cell.
- **`[!] StrandId` re-keying is a prerequisite, not optional.** Every tier decision is
  per-strand; the `FederationId`→`StrandId` migration (`gc.rs:14`) must land before
  Tier B/C routing is even expressible, and the handoff drop-attribution hole
  (`study-gc §4`) must close or Tier C's own-count safety argument is unsound under
  3-party introduction.
- **`[F]` Tier A SCC-detection cost.** Intra-vat mark-from-roots is local but not free;
  needs incremental/generational scheduling so a large vat heap doesn't pause turn
  processing. ORCA's lock-free-tracing co-design (race-freedom from caps) is the model,
  but dregg2's intra-vat concurrency story must be confirmed to admit it.
- **`[F]` No machine-checked soundness for the hybrid.** ORCA's ESOP'18 proof covers
  the *cooperative crash-free* model; it does **not** cover Byzantine peers, and
  dregg2's `Boundary.lean` does not yet model GC at all. Tier A is the only piece whose
  soundness is a near-direct port of an existing checked proof (ORCA Lemma 2). Tiers
  B/C soundness would be new Lean obligations (the tiered `Live` predicate above).
- **Open question deliberately NOT closed:** whether a *fully* distributed,
  Byzantine-safe cyclic collector exists at all. The §3 analysis strongly suggests
  **no** without either (a) a cooperative quorum (Tier B) or (b) accountability that
  reduces to consensus — i.e. cross-Byzantine cycle collection appears to **reduce to
  the revocation consensus seam** (§3), the one place dregg2 admits globalism. If so,
  lease-expiry across distrust is not a punt but a **theorem**: cross-Byzantine cyclic
  GC is consensus-hard, and dregg2 correctly refuses it.
