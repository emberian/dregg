# Study — Where Consensus Enters dregg2 (and is it coherent?)

> **Question (DEEP STUDY + design-probe):** the user senses consensus hasn't
> properly come into play. Does it? Reads `dregg2.md` §2.2 (finality tiers +
> I-confluence side-condition) + §1.6 (cross-cell ⊗) + §3 (revocation seam),
> `pdfs/decisions.md`, `pdfs/LEARNINGS-ordering-consensus.md`, the consensus
> papers (narwhal/bullshark/mysticeti/dag-rider, BEC, crdts, cryptoconcurrency,
> constitutional-consensus, blocklace, cordial-miners), and the live code
> (`blocklace/src/{finality,ordering,cross_reference,constitution}.rs`,
> `coord/src/shared_budget.rs`).
>
> Tags: `[G]` grounded-in-paper · `[C]` grounded-in-code (`file:line`) · `[F]`
> forward-design · `[T]` theorizing.

---

## 0. Verdict up front

**The thesis is CONFIRMED and sharpened, not refuted.** Consensus in dregg2 is
the **canonicity** layer (Law 2, §2.2) — strictly orthogonal to the proof
**validity** layer. A proof attests "this is *a* valid history" (de-jure
permission + conservation + chain-link); it *never* attests "this is *the*
canonical history." Canonicity is what consensus decides, and it is needed
**exactly at contention**, in precisely the three places the thesis names. The
literature converges on this hard (BEC's I-confluence iff-theorem,
CryptoConcurrency's dynamic-overspend, Narwhal/Mysticeti's "one DAG, pluggable
ordering, single-owner fast-path"). dregg2's design *states* this correctly.

**But: the user's instinct is also right.** Consensus is correct *in the design
and partly in the code*, yet it is **under-integrated at the seam that matters
most — the cross-tier atomic turn — and one impossibility corner is currently
re-derivable rather than statically forbidden.** Consensus "hasn't come into
play" because the place it must bind (the turn executor's commit-tier join) is
specified in prose (§2.2, LEARNINGS artifact-C) but **not yet enforced in the
turn pipeline**; the consensus machinery that *is* built (`blocklace/`,
`coord/shared_budget.rs`) lives *beside* the turn, not *inside* its admissibility
gate. Validity is in-circuit; canonicity is bolt-on. That is the real gap.

---

## 1. Where consensus enters — the three contention points (CONFIRMED)

The validity/canonicity split is the load-bearing distinction. Validity =
`StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` (dregg2 §7.1),
proven per-turn, content-addressed, **partition-independent**. Canonicity = which
of several individually-valid turns is *the* next one — a question a proof
**provably cannot answer** (two equivocating turns each carry a perfect validity
proof; the proof system is symmetric in them by construction). `[G]`

This is not a defect to fix — it is a theorem. A succinct proof of a state
transition is invariant under *which* concurrent transition you chose; choosing
is an extra-logical act requiring communication = consensus. So consensus enters
**exactly and only** where two valid histories contend:

1. **Multi-writer cell ordering.** A cell with `n>1` writers and a non-I-confluent
   invariant. Single-writer / I-confluent cells need *none* (tier-1; BEC Thm 3.1,
   Mysticeti-FPC single-owner fast-path). `[G]`
2. **Cross-cell atomic turns.** The γ.2 `⊗`-morphism (§1.6): N cells must agree on
   one shared turn-identity. The *binding* (CG-2 pullback over `TURN_HASH`) is
   proof; but *which* concurrent cross-cell turn wins when two contend for the same
   slot is canonicity → consensus. `[C/G]`
3. **Revocation / global-uniqueness / double-spend.** Nullifier sets, the
   revocation root, balance≥0 under concurrent debits. The non-I-confluent
   invariants (BEC Table 1). `[G]`

I-confluent / single-writer state needs **no consensus, ever** — this is
theorem-backed (BEC: hash-keyed uniqueness, G-Counter, OR-Set are I-confluent;
CryptoConcurrency: single-owner accounts are consensus-free; Mysticeti-FPC:
single-party state = reliable broadcast only). dregg2 encodes this as the
**I-confluence well-formedness side-condition** (§2.2): tier-1 is a *static type
error* unless the cell's join preserves its invariant. **This part is coherent and
correct.** `[G]`

---

## 2. Hard case A — cross-cell atomic turn across DIFFERENT tiers

> A turn writes a tier-1 (causal-only) cell **and** a tier-3 (BFT) cell. dregg2:
> "commit at the **join** of the written cells' tiers." Coherent?

**Coherent in the limit, but the framing hides a real collapse.** The join rule
(§2.2, LEARNINGS artifact-C clause 1) is correct *as a safety statement*: you
cannot finalize a tier-3 write with tier-1 evidence, so the whole turn's
**effective commit-tier = ⊔ tᵢ = tier-3**. The turn's tier-1 write is **held**
(the rollback-handler "effects held until commit," §4) until the tier-3 portion
finalizes, then released atomically (BEC *Atomicity*). `[G]`

**The sharpening the user is sensing:** *for that turn*, the tier-1 cell's write
**does become tier-3-ordered.** There is no such thing as a "half-tier-1,
half-tier-3 atomic commit" — atomicity forces the join, and the join is the *max*.
So **cross-tier-atomic does not preserve the tier-1 cell's liveness for that
turn**: a turn that touches a BFT cell **inherits BFT's partition-stall** even on
its CRDT write. The tier-1 cell does *not permanently* become tier-3 (its
*solo* turns stay liquid), but **every cross-tier turn is a tier-3 turn**. The
honest statement dregg2 should make explicit: *atomicity across tiers = the
higher tier swallows the lower for the duration of the joint turn; "cross-tier
atomic" is real but it is **not** a way to get tier-1 liveness on a tier-3-touching
operation.* This is not violated — it is **under-stated.** A developer reading
"commit at the join" may believe they keep CRDT liveness; they do not. `[F/T]`

**Disjoint reference-groups — whose quorum binds?** This is the genuinely
weak spot. `ReferenceGroup` (`ordering.rs:545`) is a *per-group view* over one
blocklace; `τ_unified` runs per group; cross-group blocks are handled by
`cross_reference.rs` as **external causal context** (`external_causal_context`,
`cross_reference.rs:154`) — i.e. *referenced, not ordered*. So today: if cell A's
quorum is group G_A and cell B's is a **disjoint** G_B, there is **no single
quorum that can finalize the joint turn.** The code can *reference* B's blocks
from G_A's view but cannot make G_B *agree* on the joint order. dregg2 §1.6
proves the *binding* (CG-2 turn-identity pullback) but the binding is a
**validity** object (everyone agrees on the hash); it is **not** a canonicity
object (a quorum that decides the order). **A cross-cell atomic turn across
disjoint reference-groups requires the union G_A ∪ G_B to act as one quorum for
that turn — i.e. an ad-hoc joint committee — and dregg2 specifies no protocol for
forming it.** `[C]` This is the concrete sense in which "consensus hasn't come
into play": the `⊗` is proven at the validity layer and *assumed* at the
canonicity layer. **Recommendation: a cross-group turn must form the
join-group `G_A ∪ G_B` and commit at `max(tier_A, tier_B)` under that union's
quorum; absent a shared root this needs an explicit committee-formation step
(constitutional `AmendRoutes`-style, `constitution.rs`).** `[F]`

---

## 3. Hard case B — non-pairwise overspend (cryptoconcurrency)

> Three individually-valid spends jointly overspend. Does per-cell finality catch
> it, or miss it (pairwise blindness)?

**CAUGHT — and this is the strongest-built part.** `coord/src/shared_budget.rs`
implements a CryptoConcurrency-style **COD (overspend detector)** as a genuine
**sum/coverage predicate over the whole observed set**, not pairwise:
`is_overspent() = total_spent() > total_balance` (`shared_budget.rs:388`), where
`total_spent` aggregates **all** debits across **all** participants observed in
the blocklace (`sync_from_blocklace`, `:406`). On overspend it `escalate()`s to
tier-3 Closing (`:532`), and `resolve_with_ordering()` (`:551`) replays the
debits **in τ-order from Cordial Miners**, first-fit accepting until the balance
is exhausted, rejecting the rest. This is *exactly* CryptoConcurrency's
COD-Close→Consensus→snapshot, and it defeats the Fig-4 three-spends-on-balance-2
attack a pairwise detector misses. `[C/G]`

**Caveat (the same under-integration):** the COD is a **separate side-table
keyed on a resource**, driven by `sync_from_blocklace`, **not** the cell's
`CellProgram` admissibility gate. So multi-party overspend is caught *reactively*
by a coordinator that scans the DAG, **not** *by the turn proof* (`StepInv` is
per-turn and cannot see the concurrent set — by §1, it provably can't). That is
correct architecturally (coverage is a canonicity question, not a validity one)
but means the COD must be **wired to every shared-balance cell's escalation
trigger**, and the doc should state that a shared-`balance≥0` cell is
**ill-typed at tier-1** (§2.2 says so) and **must** register a COD. The mechanism
exists; the *binding of COD-to-cell* is the loose wire. `[C/F]`

---

## 4. Hard case C — revocation as "root-epoch agreement"

> Genuinely weaker than full consensus, or secretly needs it?

**Genuinely weaker — confirmed, with a precise boundary.** dregg2 §3 calls
revocation "the lone consensus seam," needing only **root-epoch agreement**: a
STARK *non-membership* proof against an *attested revocation root*. The weakening
is real: a revocation **set** is a G-Set keyed by `H(credential)` → **I-confluent
by BEC Table 1** (hash-keyed uniqueness is the canonical tier-1-safe CvRDT). So
*adding* a revocation is a monotone, consensus-free CRDT join; the **only**
consensus need is agreeing **which epoch's root** a given proof is checked
against — a far weaker object than ordering arbitrary transactions (it is
*one* periodically-published commitment, not a per-op total order). `[G]`

**Where it secretly needs more:** the *freshness* guarantee. Non-membership
against root `R_epoch=k` says "not revoked **as of epoch k**" — a verifier on a
partition holding a stale root accepts a since-revoked credential. So
root-epoch agreement is weaker than full consensus but is **not free**: it needs a
**liveness/recency floor** on root publication, which under partition is exactly
where it stalls (you cannot prove a *negative* — non-revocation — about events
you haven't seen). dregg2 is honest about this ("Prefer short expiry + renewal
over revocation; any design claiming clean global revocation under local-first is
lying," §3). **Verdict: weaker, correctly identified, and the honesty note is
load-bearing — revocation is the one place "local-first + global negative-fact"
genuinely cannot be fully reconciled, and the design says so.** `[G]`

---

## 5. Lurking impossibilities — does any corner violate one?

**FLP.** No violation. dregg2 never claims async deterministic agreement with
liveness: tier-3/4 "stall, resume after GST" (§2.2 table) — i.e. it sacrifices
**liveness** under async, keeping safety. Tier-1/2 are *consensusless* (no
agreement claimed, so FLP doesn't bind). Clean. `[G]`

**CAP.** No violation, and the menu is *built around* the wall. Tier-1/2 = AP
(never block, available under partition, but cannot enforce non-I-confluent
invariants); tier-3/4 = CP (consistent, but stall under partition). **No single
tier is both** — the LEARNINGS doc names this "the CAP-shaped wall the menu is
honestly built around, not a gap to be closed." `[G]`

**The BEC I-confluence theorem (the dangerous one).** This is where a violation
*could* hide, and the design's defense is a **static type error**, not a runtime
guard. The forbidden corner: **tier-1 (partition-tolerant, never-blocks) + a
non-I-confluent invariant.** BEC Thm 3.1 proves this is *unrealizable* — no
algorithm escapes it (the proof is information-theoretic: put the two conflicting
txns on the only two correct replicas, Byzantine-silence the rest, async-delay,
heal → forced merge violates `I`). dregg2 §2.2 correctly declares this a **static
type error** via the I-confluence well-formedness side-condition. `[G]`

**THE ONE LIVE RISK:** is that side-condition **actually enforced**, or only
*documented*? It is a `[G]`-claim in the doc and a prose contract in LEARNINGS
artifact-A (`FinalityRule::admits` runs the I-confluence check), **but I found no
code that statically rejects a tier-1 cell with a non-I-confluent
`CellProgram`.** The `CellProgram` catalog (`program.rs`) has the *vocabulary* to
express `balance≥0` (`Gte`, `SumEquals`, `FieldDelta`) and the finality machinery
(`blocklace/`) has tiers, but **the type-level join between "this cell's invariant
lattice" and "this cell's finality tier" is not wired** — nothing stops a
developer declaring a `balance≥0` cell at tier-1. If that path exists at runtime,
**dregg2 *would* violate BEC Thm 3.1** (it would claim a partition-tolerant,
never-blocking cell preserving a non-I-confluent invariant — exactly the
impossible object). **This is the genuine impossibility the design currently
risks violating — not in spec, but in the unenforced gap between spec and code.**
The fix is the `admits` gate (LEARNINGS artifact-A) made a real static check on
cell creation, keyed off an I-confluence classifier over the `StateConstraint`
set. `[C/F]`

---

## 6. Net — where it stands

| Claim | Verdict |
|---|---|
| Consensus = canonicity, orthogonal to proof/validity | **Confirmed**, theorem-backed (a proof is symmetric in equivocating valid histories) |
| Enters at exactly (1) multi-writer, (2) cross-cell atomic, (3) revoke/uniqueness/double-spend | **Confirmed** (BEC + CryptoConcurrency + Mysticeti/Narwhal converge) |
| I-confluent/single-writer needs none (tier-1) | **Confirmed & correct** in spec |
| Cross-tier atomic = "commit at the join" | **Coherent but under-stated**: the join is the *max*; the lower tier loses its liveness *for that turn*; "cross-tier atomic" ≠ "tier-1 liveness on a tier-3-touching op" |
| Cross-cell across **disjoint reference-groups** | **Gap**: binding is proven (validity, CG-2) but no protocol forms the joint quorum (canonicity). Needs `G_A ∪ G_B` committee-formation |
| Non-pairwise multi-party overspend | **Caught** — real coverage/sum predicate (`shared_budget.rs` COD), τ-ordered resolution. Strongest-built part. But COD-to-cell binding is a loose wire |
| Revocation = root-epoch agreement | **Genuinely weaker** than full consensus (I-confluent G-Set + one epoch commitment); recency floor under partition is the irreducible residue, and the design says so |
| FLP / CAP | **No violation** — liveness sacrificed under async (tiers 3/4 stall); CAP wall is the *design axis*, not a bug |
| **BEC I-confluence** | **The one live risk**: spec forbids the impossible corner as a static type error, but the `admits` gate is **not wired in code** — an unenforced tier-1 + non-I-confluent cell *would* violate BEC Thm 3.1 |

**Why the user senses consensus "hasn't come into play":** validity (the proof,
`StepInv`) is in-circuit, per-turn, soundness-critical — and built. Canonicity
(consensus, the tiers) is correct *in the design* and partially built
(`blocklace/`, the COD), but it **lives beside the turn, not inside its
admissibility gate**: the cross-tier join is not enforced by the executor, the
COD is not bound to its cell's finality rule, and the I-confluence side-condition
is documented but not type-checked. The architecture is coherent; the
**consensus↔turn integration seam is the genuinely unbuilt part** — which is
exactly consistent with `decisions.md` §7 putting *step-completeness* (validity)
first and treating finality wiring as downstream. The recommendation is to make
three prose contracts into real gates: (a) `FinalityRule::admits` as a static
I-confluence check at cell creation; (b) executor enforcement of commit-tier =
⊔ written-cell tiers with held effects; (c) COD registration mandatory for any
shared non-I-confluent cell, with disjoint-group turns forming an explicit joint
committee.
