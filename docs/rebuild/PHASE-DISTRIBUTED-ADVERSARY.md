# PHASE — The Distributed-Adversary / Byzantine / GST / UC Model

> **Provenance.** 2026-05-30, read-only research agent (Claude Opus 4.8, 1M).
> Scope: do the four honest-OPEN `sorry`s in `World.lean` / `Liveness.lean` /
> `Spec/Lifecycle.lean` that name a *distributed-adversary / Byzantine /
> partial-synchrony (GST) / universally-composable* model have, in `pdfs/`, a
> **formalizable** model to close them? Or is it a genuine corpus gap?
> **No `.lean` file was edited. `lake build` was not run.** This doc is the only
> artifact produced.
>
> **Verdict in one line:** the corpus has the *avoidability / impossibility*
> half (BEC I-confluence, CryptoConcurrency, the DAG-BFT line, FLP/CAP framing)
> in depth, and that half is already *cashed out* as PROVED theorems in `World`
> and `Liveness`. The four OPENs need the *protocol-positive* half — a formal
> Byzantine quorum-intersection theorem, a partial-synchrony/GST liveness model,
> and a computability/Turing model for the undecidability dual. **Three of those
> are genuine corpus GAPS** (no Canetti-UC, no DLS88, no FLP-paper, no PBFT/
> HotStuff/Tendermint/Streamlet, no quorum-systems paper in `pdfs/`); the fourth
> (the undecidability `sorry`s) is groundable *now* from Mathlib alone with **no**
> external paper. Be skeptical: the user's suspicion is correct.

---

## 1. The four OPENs (precise obligations, `file:line`)

| # | Theorem | Location | What the `sorry` actually needs |
|---|---------|----------|---------------------------------|
| O1 | `quorum_intersection_safety_OPEN` | `metatheory/Dregg2/World.lean:263` | An **adversary/honesty model** over `votersFor` (which voters are Byzantine), a **conflict relation** on blocks, and the `n>3f` quorum-intersection pigeonhole. The docstring (`:256–262`) is explicit: "the bare `World` interface … cannot establish it … belongs with the protocol, not the network oracle." |
| O2 | `liveness_after_gst_OPEN` | `metatheory/Dregg2/World.lean:287` | A **partial-synchrony / GST model** (the `clock` made meaningful for message-delay bounds) + an **honest-supermajority** assumption. Docstring (`:281–286`): "Requires the GST + honesty model the interface deliberately omits (asynchrony is the adversary's, not a law)." |
| O3 | `dead_undecidable` / `distributed_death_not_co_witnessable` | `metatheory/Dregg2/Liveness.lean:216` and `metatheory/Dregg2/Spec/Lifecycle.lean:386` (the latter delegates to the former; **same obstruction, two sites**) | A **computability/Turing model**: refute *every* `decide : LivenessGraph → CellId → Bool` that soundly-and-completely decides `Dead = ¬reachable`. The `sorry` comment (`Liveness:220–222`) names it: "diagonalization against a computability model not present in the imported modules." |
| O4 (PROVED, listed for contrast) | `crossvat_cycle_leaks` | `metatheory/Dregg2/Liveness.lean:389` | **Already PROVED** (no `sorry`). The "cross-vat cycle-leak" theorem the task brief points at is *closed* — it is proved directly from the `SoundLocalCollector.sound` side-condition + the cycle giving each node an inbound edge. The genuine OPEN *near* it is O3 (`dead_undecidable` at `:216`), not the leak itself. |

**Correction to the brief.** The brief lists "`Liveness.lean:~216` — cross-vat
cycle-leak (dead-not-co-witnessable under partition)" as an OPEN. Two distinct
things live there and only one is open:
- `crossvat_cycle_leaks` (`:389`) — the cross-vat-cycle *leak* — is **PROVED**.
  It is a constructive, finite, local argument; it needs **no** distributed-
  adversary model and is **done**.
- `dead_undecidable` (`:216`) — distributed deadness is **not co-witnessable** —
  is the genuine `sorry`. Its obstruction is **computability (Turing)**, not
  Byzantine/GST. `Spec/Lifecycle.lean:386` is the same statement re-exported and
  carries the same `sorry`. So O3 is *one* mathematical obligation appearing at
  two sites.

This matters for the verdict: O3/O3' are NOT a "distributed-adversary model"
gap at all — they are a **computability-theory** gap, and a *much* cheaper one
(see §4). Only **O1 and O2 are genuinely the Byzantine/GST model** the phase is
named for.

---

## 2. What `World.lean` already PROVES (the model that exists)

`World` is an **uninterpreted oracle with laws** — the exact `CryptoKernel`
shape. It is *not* empty; it already closes the network-monotonicity half:

- **Interface** (`World.lean:75–97`): `clock : Unit → Nat`, `recv : Nat → List Msg`,
  `rand : Nat → Nat`, and **one law**: `recv_mono` (append-only delivery — the
  adversary may delay/reorder but cannot un-deliver).
- **PROVED facts**: `votersFor_length_mono` (`:153`), `quorum_monotone` (`:179`),
  `committedByQuorum_mono` (`:194`), `world_no_downgrade` (`:244`),
  `quorumRule` as a lawful `FinalityRule` (`:218`). I.e. **"a quorum commit does
  not un-happen as the log grows"** is fully proved.
- **Inhabited**: `Reference` instance (`:304–335`) witnesses the laws are
  satisfiable (theorems non-vacuous).

So the *safety-monotonicity* spine over the network oracle is real. What is
missing is everything that needs to talk about **who is honest** (O1) and
**when messages arrive** (O2) — and the interface *deliberately* omits both:
`recv_mono` is the *only* law, and asynchrony is "the adversary's, not a law."

---

## 3. `pdfs/` inventory — HAVE vs DO-NOT-HAVE for this model

### 3a. The relevant clusters that ARE present

(From `pdfs/INDEX.md §13–15`, `LEARNINGS-ordering-consensus.md`,
`docs/rebuild/study-consensus.md`. Filenames verified by `ls`.)

- **Byzantine eventual consistency / I-confluence (the impossibility line):**
  `byzantine-eventual-consistency-2012.00472.pdf` (Kleppmann & Howard — the
  I-confluence **iff** theorem, the brutally-simple async-partition impossibility
  proof), `making-crdts-byzantine-fault-tolerant.pdf`,
  `proof-carrying-crdts-byzantine-update-papoc25.pdf`,
  `extend-only-directed-posets-byzantine-crdts.pdf`,
  `bounding-byzantine-impact-open-crdt-systems.pdf`,
  `byzantine-ft-crdts-from-cryptocurrencies-2311.13936.pdf`.
- **Consensus *avoidability* (when consensus is/ isn't needed):**
  `cryptoconcurrency.pdf` (single-owner = consensus-free; shared = reduces *from*
  consensus; dynamic overspend-escalation).
- **DAG-BFT (protocol family, prose only):** `narwhal-and-tusk-dag-bft-2105.11827.pdf`,
  `bullshark-dag-bft-2201.05677.pdf`, `cordial-miners.pdf`, `blocklace.pdf`,
  `blocklace-byzantine-repelling-universal-2402.08068.pdf`,
  `sui-lutris-broadcast-and-consensus-2310.18042.pdf`,
  `sui-shared-objects-owned-vs-shared-2406.15002.pdf`,
  `dyno-dynamic-bft.pdf`, `adversary-majority.pdf`, `2304.14701` (permissionless
  consensus, Lewis-Pye/Roughgarden).
- **Accountability / forensics:** `cft-forensics-byzantine-accountability-2305.09123.pdf`,
  `themis-order-fairness-byzantine-consensus-2021-1465.pdf`,
  `sok-consensus-fair-message-ordering-2411.09981.pdf`.
- **Verified-distributed-systems *templates* (the l4v analogs):**
  `verdi-verified-distributed-pldi15.pdf`, `velisarios-bft-coq.pdf` (**BFT in Coq**),
  `ironfleet-distributed-systems.pdf`, `disel-distributed-separation-logic.pdf`,
  `igloo-refinement-separation-logic-oopsla20.pdf`.
- **UC-flavoured (application, not framework):** `uc-zk-smart-contracts-2022-670.pdf`,
  `kachina-private-contracts.pdf` (Midnight). These *use* a UC ideal-functionality
  for ZK contracts; they are **not** Canetti's UC framework and do not give a
  reusable composition theorem.

### 3b. The clusters that are ABSENT (verified by `ls`/grep — **GAPS**)

Searched `pdfs/` (249 PDFs) for: `canetti|composab|simulation|ideal|functionality`,
`dls88|flp|fischer|lynch|paterson|gst|stabiliz|dwork`, `quorum|dissemination|
malkhi|reiter`, `pbft|castro|hotstuff|tendermint|streamlet|casper|responsive`.
**Zero hits** (the one `castro` is `role-parametric-session-types-in-go-castro.pdf`,
unrelated). Concretely missing:

- **Universal Composability framework** — Canetti, *Universally Composable
  Security* (FOCS'01 / eprint 2000/067) and the UC-with-global-setup / GUC line.
  **Absent.** (`uc-zk-smart-contracts` *applies* UC; it does not define it.)
- **Partial-synchrony / GST** — Dwork–Lynch–Stockmeyer, *Consensus in the
  Presence of Partial Synchrony* (JACM'88, "DLS88"). **Absent.** This is the
  canonical source of the GST model O2 needs.
- **FLP impossibility** — Fischer–Lynch–Paterson (JACM'85). **Absent** as a
  paper (the *conclusion* is cited in `study-consensus §5`, but no formal model).
- **Quorum systems** — Malkhi–Reiter *Byzantine Quorum Systems*, and the generic
  `Q1∩Q2≠∅` / `n>3f` masking-quorum intersection lemma. **Absent.** O1 IS this
  theorem.
- **Classic + modern BFT protocols** — PBFT (Castro–Liskov), HotStuff,
  Tendermint, Streamlet, Algorand-BA. **All absent.** (Only DAG-BFT *constructions*
  are present, and only as prose, not as a formal safety/liveness model.)
- **Long-lived / responsive consensus, accountable-BFT formal models** — present
  only as the forensics SoK (`cft-forensics-…`), which gives accountability, not
  a quorum-intersection or GST-liveness theorem.

### 3c. What the existing study docs already concluded

`study-consensus.md §5` and `LEARNINGS-ordering-consensus.md` explicitly record:
- FLP / CAP are **named and respected**, not violated — "liveness sacrificed
  under async (tiers 3/4 stall)" — but treated as *design axioms*, never as
  *formalized models*.
- The **hard BFT floor** ("`n ≥ 3f+1`, partial synchrony for liveness, `Ω(f²)`
  messages") is cited from CryptoConcurrency's intro and BEC §1 — i.e. **second-
  hand, no primary partial-synchrony paper backs it.**
- `OPEN-PROBLEMS.md` "Papers to FETCH" lists MPST/choreography gaps but does
  **not** even list the BFT/GST/UC gap — meaning this phase surfaces a corpus
  hole the prior register missed. (It lists `#5 IVC`, `#2 cross-group blocking`
  as impossibilities, but the *partial-synchrony liveness model* is nowhere
  named as a fetch target.)

---

## 4. Per-OPEN verdict

### O1 — `quorum_intersection_safety_OPEN` (World.lean:263) — **GAP (named-paper needed), but the core lemma is *formalizable now* with a small honest-set extension.**

Two layers:
1. **The pure quorum-intersection pigeonhole** (`|Q₁|+|Q₂| > n ⇒ Q₁∩Q₂≠∅`, and
   with ≤ f Byzantine and threshold `> ½(n+f)`, the intersection contains an
   *honest* voter) is **elementary finite combinatorics over `List Nat`/`Finset`**.
   This is **formalizable now from Mathlib alone** — it needs *no* external paper.
   The current statement already supplies `hbound` (`World.lean:270`) as the
   protocol-given membership bound; the conclusion (`∃ voter ∈ both`) is a
   pigeonhole on `votersFor`. **This specific theorem can likely be CLOSED today**
   by adding the `n>3f` arithmetic and a `Finset.exists_mem_inter`-style step —
   the docstring's claim that it "needs the adversary model" *overstates* what the
   stated conclusion (mere non-empty intersection) requires. The *honest*-voter
   strengthening (intersection contains a non-Byzantine voter ⇒ a Byzantine node
   double-voted ⇒ slashable) is what needs the honesty model.
2. **The full BFT *safety* theorem** ("two quorums for conflicting blocks ⇒ a
   contradiction under `n>3f`, ≤f Byzantine") needs: (a) a `Byzantine : Nat → Prop`
   predicate on voters with `|{v | Byzantine v}| ≤ f`, (b) an honest-voter
   "votes once per height" law, (c) a conflict relation on blocks. These are a
   *modelling* choice dregg2 can make itself, but the *reference* model to copy is
   **Malkhi–Reiter Byzantine Quorum Systems** (intersection-with-honest-witness)
   — **a paper we do NOT have.** `velisarios-bft-coq.pdf` (present) is the closest
   *mechanization template* (PBFT-family safety in Coq) and would guide the Lean
   shape even without Malkhi–Reiter.

**Verdict O1:** the *stated* `sorry` (non-empty intersection) is **groundable
now, no paper**. The *intended* BFT safety theorem behind it is a **GAP** —
fetch **Malkhi–Reiter, *Byzantine Quorum Systems* (Distributed Computing 1998)**;
use `velisarios-bft-coq.pdf` as the mechanization template.

### O2 — `liveness_after_gst_OPEN` (World.lean:287) — **GENUINE GAP. Not formalizable from what we have.**

This needs a **partial-synchrony model**: a GST round `τ_GST` after which message
delay is bounded by `Δ`, the `World.clock` related to real delivery, and an
**honest-supermajority** assumption that *enough* honest votes are eventually
`recv`'d. The `World` interface has **no delay bound and no honesty** — it is
(by design) "possibly fully asynchronous," and under full asynchrony the
statement is **false** (FLP: the adversary delays all votes forever). So O2 is
**not provable as stated** and cannot become provable without *adding new laws*
to `World` encoding GST + honest liveness.

The model to copy is **Dwork–Lynch–Stockmeyer, *Consensus in the Presence of
Partial Synchrony* (JACM 1988)** — the GST definition itself — paired with a
modern responsive-BFT liveness argument (HotStuff/Streamlet style). **We have
NONE of these.** Even *with* DLS88, formalizing GST-liveness in Lean is **genuine
research** (it is among the hardest things in `verdi`/`velisarios`/`ironfleet`,
each of which dedicates a paper to a *single* protocol's liveness). 

**Verdict O2:** **genuine corpus GAP *and* research-grade even with the paper.**
Fetch **DLS88** (the GST model) and **HotStuff (Yin et al., PODC'19)** or
**Streamlet (Chan–Shi, 2020)** (a clean responsive-liveness proof to port).
Honest recommendation: keep O2 as an honest `OPEN` and instead extend `World`
with an *assumed* GST-liveness law (the same move `recv_mono` makes for safety) —
i.e. make eventual-honest-delivery an **oracle obligation the runtime
discharges**, not a Lean theorem. That is the dregg2-coherent resolution and
needs no paper: it turns O2 from "prove liveness" into "*assume* the GST law,
*derive* `∃ r block, committedByQuorum …`" — a one-line consequence of a new
`World` field `gst_liveness : ∃ r, quorumReached (votesOf (recv r)) cfg b`. That
is intellectually honest (it matches how `recv_mono` is assumed) and **closes the
`sorry` without claiming to have proved an async-liveness theorem we cannot.**

### O3 / O3' — `dead_undecidable` (Liveness.lean:216) + `distributed_death_not_co_witnessable` (Spec/Lifecycle.lean:386) — **NOT a distributed-adversary gap. Formalizable NOW from Mathlib computability; no paper needed.**

These are mis-filed under "distributed adversary." The obstruction is **pure
computability**: refute every `decide : LivenessGraph → CellId → Bool` deciding
`Dead = ¬reachable`. As *currently stated* the theorem quantifies over an
**arbitrary** `LivenessGraph` whose `edge : CellId → CellId → Prop` is an
arbitrary (undecidable) relation. There are two honest paths:

1. **Cheap and immediate (recommended):** the *stated* theorem ("there is no
   uniform sound-and-complete decider over ALL graphs") is actually **provable by
   a short diagonal/cardinality argument *within Lean/Mathlib*** — encode a
   Turing machine's halting predicate into `edge` (Mathlib has `Computability`/
   `Turing`, `Nat.Partrec`, `ComputablePred`, and `Turing.halting` undecidability),
   reduce halting to `reachable`, conclude `Dead` has no decider. This is **a real
   but standard mechanization**, **no external paper required** — it is the same
   genre as Mathlib's existing undecidability-of-halting development. Effort:
   *days*, not research.
2. **Even cheaper (if the above is too heavy):** restate the obligation as a
   *relative* impossibility — "no decider that reads only finite local evidence" —
   which is `crossvat_cycle_leaks`'s shape and is **already proved**. The
   absolute-undecidability `sorry` could then be retired in favour of the
   relative one the design actually uses (`reclaim_by_lease`).

**Verdict O3/O3':** **NOT a corpus gap and NOT a distributed-adversary model.**
It is a Mathlib-computability exercise (halting ↪ reachability). Groundable now.
The two sites (`Liveness:216`, `Lifecycle:386`) collapse to one lemma + one
delegation. This is the **lowest-hanging of the four**.

---

## 5. Formalization plan (what becomes provable, and how hard)

The `World` portal is the intended home and is already shaped for this: an
oracle whose *only* commitments are stated laws. The pattern for each OPEN is to
decide **"new PROVED theorem"** vs **"new assumed oracle law (like `recv_mono`)."**

### Tier A — formalizable NOW, no external paper (do these)

- **O3 / O3' (undecidability).** Add a `Dregg2.Computability` lemma:
  `reachable` is the reflexive-transitive image of `edge`; instantiate `edge`
  from a Turing machine via Mathlib `Turing`/`Nat.Partrec`; reduce `halting` to
  `reachable`; conclude no `decide` is sound-and-complete. Then `Lifecycle:386`
  becomes a one-line `exact Liveness.dead_undecidable`. **Difficulty: medium
  (Mathlib computability boilerplate). No paper.**
- **O1 — the *stated* non-empty-intersection conclusion.** Pure pigeonhole.
  Strengthen `hbound` reasoning with `n>3f` and `Finset`/`List` counting; the
  conclusion `∃ voter ∈ votersFor b₁ ∧ ∈ votersFor b₂` follows by a counting
  argument (`|Q₁|+|Q₂| > n`). **Difficulty: easy–medium. No paper for the bare
  lemma.** (Caveat: this proves *intersection*, not yet *the BFT contradiction*.)

### Tier B — formalizable now *as an assumed `World` law* (the honest, dregg2-coherent move)

- **O2 — GST liveness.** Do **not** try to prove async liveness (impossible /
  research). Instead add a `World`-class field, mirroring `recv_mono`:
  ```
  gst_liveness : ∀ (votesOf …) (cfg …),
      ∃ (r : Nat) (b : BlockId), committedByQuorum votesOf r cfg b
  ```
  guarded by an explicit `[PartialSynchrony]` / honest-supermajority hypothesis.
  Then `liveness_after_gst_OPEN` is discharged by `World.gst_liveness` — exactly
  as the safety side is discharged by `recv_mono`. This is **intellectually
  honest**: it *names* GST + honesty as an environment obligation the runtime
  guarantees, not a Lean theorem, and it removes the `sorry` without overclaiming.
  **Difficulty: trivial once the law is stated; the *honesty* of the law is the
  whole point.** **No paper needed to state it**; a paper (DLS88) is needed only
  if one ever wants to *prove* it against a modelled protocol.

### Tier C — needs an external paper AND is research-grade (do NOT promise)

- **O1 — the full BFT safety theorem** (conflicting quorums ⇒ contradiction
  under `n>3f`, ≤f Byzantine, honest-vote-once). Needs a modelled adversary +
  honesty predicate + conflict relation. **Fetch Malkhi–Reiter (Byzantine Quorum
  Systems);** template: `velisarios-bft-coq.pdf`. **Difficulty: a focused
  formalization (weeks), tractable with the paper — this is what `velisarios`
  did in Coq for PBFT.**
- **O2 — *proving* (not assuming) GST liveness** against a modelled τ-BFT
  protocol. **Fetch DLS88 + HotStuff/Streamlet.** **Difficulty: genuine research
  even with the papers** — every verified-distributed-systems paper we *do* have
  (`verdi`, `velisarios`, `ironfleet`) spends its entire length on one protocol's
  liveness. dregg2 should not claim this; Tier-B (assume the law) is the right
  call until/unless a dedicated effort is funded.

---

## 6. Papers to FETCH (named, NOT fetched — `$ANNAS_SECRET_KEY` exists but unused here)

For O1 (BFT quorum safety):
1. **Malkhi, Reiter — *Byzantine Quorum Systems*** (Distributed Computing 11(4),
   1998). The `Q1∩Q2` masking-quorum intersection-with-honest-witness lemma. ← O1.
2. *(optional, foundational)* **Castro, Liskov — *Practical Byzantine Fault
   Tolerance*** (OSDI'99) — the canonical `n=3f+1` safety/liveness pairing.

For O2 (GST / partial-synchrony liveness):
3. **Dwork, Lynch, Stockmeyer — *Consensus in the Presence of Partial
   Synchrony*** (JACM 35(2), 1988). The GST model itself. ← O2 (mandatory if ever
   proving, not assuming).
4. **Yin, Malkhi, Reiter, Gueta, Abraham — *HotStuff*** (PODC'19) **or**
   **Chan, Shi — *Streamlet*** (2020) — a clean responsive-liveness proof to port.
5. *(foundational, for the impossibility framing)* **Fischer, Lynch, Paterson —
   *Impossibility of Distributed Consensus with One Faulty Process*** (JACM'85).

For the UC half (only if the composition theorem is ever wanted — currently no
OPEN strictly needs it; `World` is a *standalone* oracle, not a UC functionality):
6. **Canetti — *Universally Composable Security: A New Paradigm for
   Cryptographic Protocols*** (FOCS'01 / eprint 2000/067) + **Canetti, Dodis,
   Pass, Walfish — *UC with Global Setup*** (TCC'07). These would let `World` +
   `CryptoKernel` be stated as UC ideal functionalities with a composition
   theorem; **none of the four OPENs require it** — it is a *nice-to-have* for a
   future "the whole node UC-realizes the spec" claim, not a blocker.

**O3/O3' needs NO paper** — it is Mathlib computability.

---

## 7. Bottom line (skeptical answer to "do we have the model?")

**Mostly no, and that is the honest finding — but it matters less than it looks,
because two of the four OPENs are not actually the named model:**

- **O3 + O3' (2 of 4):** NOT a distributed-adversary gap at all — a **computability**
  obligation, **closeable now from Mathlib, no paper.** Mis-filed by the brief.
- **O1 (stated form):** the bare intersection lemma is **closeable now, no paper**
  (pure pigeonhole); the *full BFT safety* version is a **real GAP** needing
  Malkhi–Reiter, but is a *tractable* formalization (cf. `velisarios`).
- **O2:** **genuine corpus GAP** (no DLS88, no partial-synchrony paper) **and**
  research-grade to *prove*. The dregg2-coherent, honest resolution is to **assume
  the GST-liveness law as a `World` oracle field** (exactly like `recv_mono`) —
  which needs **no paper** and removes the `sorry` without overclaiming.

So: the corpus has the **impossibility / avoidability** half richly (BEC,
CryptoConcurrency, DAG-BFT, FLP/CAP framing) and **zero** of the **protocol-
positive** half (no Canetti-UC, no DLS88, no FLP-paper, no PBFT/HotStuff/
Tendermint/Streamlet, no Malkhi–Reiter quorum systems). The user's suspicion —
"we may genuinely NOT have the model" — is **correct for O2 and the strong form
of O1**, and **wrong for O3/O3'** (those were never that model). The single
highest-value, paper-free next step is **O3/O3' via Mathlib computability**;
the single most honest move on O2 is **promote GST-liveness to an assumed
`World` law** rather than fetch-and-prove.

---

### Appendix — exact citations used

- Lean OPENs: `metatheory/Dregg2/World.lean:263`, `:287`;
  `metatheory/Dregg2/Liveness.lean:216` (`dead_undecidable`), `:389`
  (`crossvat_cycle_leaks`, **PROVED**); `metatheory/Dregg2/Spec/Lifecycle.lean:386`.
- `World` PROVED spine: `World.lean:97` (`recv_mono` law), `:179`
  (`quorum_monotone`), `:194` (`committedByQuorum_mono`), `:244`
  (`world_no_downgrade`).
- Corpus HAVE: `pdfs/byzantine-eventual-consistency-2012.00472.pdf`,
  `pdfs/cryptoconcurrency.pdf`, `pdfs/narwhal-and-tusk-dag-bft-2105.11827.pdf`,
  `pdfs/bullshark-dag-bft-2201.05677.pdf`, `pdfs/velisarios-bft-coq.pdf`,
  `pdfs/verdi-verified-distributed-pldi15.pdf`,
  `pdfs/ironfleet-distributed-systems.pdf`,
  `pdfs/cft-forensics-byzantine-accountability-2305.09123.pdf`,
  `pdfs/uc-zk-smart-contracts-2022-670.pdf` (UC *application*, not framework).
- Corpus ABSENT (grepped 249 PDFs, zero hits): Canetti UC, DLS88, FLP,
  Malkhi–Reiter quorum systems, PBFT/HotStuff/Tendermint/Streamlet.
- Prior conclusions: `docs/rebuild/study-consensus.md §5` (FLP/CAP respected, not
  formalized; BFT floor cited second-hand), `pdfs/LEARNINGS-ordering-consensus.md`
  ("Fundamental limits"), `docs/rebuild/OPEN-PROBLEMS.md` (does NOT list the
  BFT/GST/UC gap — this phase surfaces it).

---

## UPDATE (2026-05-30, autonomous wave L/M/N — all three recommendations executed, reconcile-build green)

Every Tier-A/Tier-B recommendation above was carried out the same session; full `lake build`
green at 3041 jobs, each result `#assert_axioms`-clean:

- **O3 + O3' — CLOSED (Tier A, no paper).** `dead_undecidable` was found **classically false as
  originally stated** (it quantified over an *arbitrary* `decide`, which `Classical.decide` always
  supplies — a latent vacuity). Restated to quantify over **computable** deciders and proved by the
  exact halting reduction §5 recommended: a `haltGraph` gadget + `ComputablePred.halting_problem`
  (`Mathlib.Computability.Halting`). `Spec/Lifecycle.distributed_death_not_co_witnessable` collapsed to
  the predicted one-line delegation. A downstream re-export, `Exec/CellLiveness.death_not_decidable`,
  carried the *same* vacuous old form and was likewise restated to the genuine computable form.
- **O1 — CLOSED (intersection core, Tier A) + honestly scoped (Tier C deferred).** The bare
  quorum-intersection proved by real pigeonhole (`Finset.card_union_add_card_inter` + `omega`); the
  `hbound` hypothesis (which was *contradictory as written*) was restated to the honest
  union-cardinality bound. The full honest-vote-once BFT-safety contradiction (needs Malkhi–Reiter) is
  left a precise prose note — **not** a `sorry`.
- **O2 — CLOSED via the Tier-B assumed-law move.** A `gst_liveness` field was added to the `World`
  class — the FLP-respecting partial-synchrony oracle law §5 recommended, documented exactly like
  `recv_mono`; `liveness_after_gst` discharges from it in three lines, and the `Reference` instance was
  updated to provide it honestly.

**Net:** all four named OPENs are now closed or honestly-bounded **without fetching any of the named
papers.** The genuine remaining research (off the critical path, honestly boundaried) is the *full* BFT
safety theorem (O1's contradiction half → Malkhi–Reiter) and a *from-scratch proof* of GST-liveness
(O2 → DLS88+HotStuff). Recurring lesson of the wave: **three of the four OPEN `sorry` sites were
false-or-contradictory as stated**, not merely hard — latent vacuity that the honesty discipline and
the reconcile build surfaced.
