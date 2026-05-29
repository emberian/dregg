# STUDY — five ACM papers vs dregg2's claimed-novel pieces (the honest scoop check)

**For:** the rebuild-driving agent (`docs/rebuild/dregg2.md`).
**What this is:** a novelty/scoop audit of five just-acquired papers that sit unusually close to dregg2's thesis,
read against dregg2's genuinely-new claims (`dregg2 §1.1` CDT, `§2.2/§2.3` finality-tier + I-confluence,
`§3` keys-as-caps, `§5` schema migration, `§7` proof architecture; `discoveries-2 §6`; `decisions §0`).
Tags: `[G]` grounded-in-paper · `[F]` forward-design · `[T]` theorizing.

**The bottom line up front:** the on-the-nose paper (Marx/Jacob/Hartenstein, "Proof-Carrying CRDTs") is
**CONFIRMING, not SCOOPING.** It is independent convergence on the *core move* — attach a recursive
SNARK/PCD proof to a CRDT update so a Byzantine peer can validate it succinctly without the full history —
which validates dregg2's direction strongly. But it solves a **strictly narrower** problem: their attested
predicate is *equivocation-tolerant update-validity* (the predicate must not depend on concurrent updates),
on a **single CRDT, with no value-conservation, no authority-in-proof (explicitly out of scope), no cell/cap
frame, no cross-cell binding, no coinductive soundness statement, and recursion-friendly only**. dregg2's
distinctive object — the full `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` step-complete
turn — is precisely the thing they flag as "important future work." So: **direction confirmed and de-risked;
the hard, novel parts remain dregg2's.**

---

## 1. Proof-Carrying CRDTs (Marx, Jacob, Hartenstein, PaPoC '25) — the novelty verdict `[G]`

### What they EXACTLY prove/build
A proof-carrying-data (PCD) wrapper for Byzantine-tolerant CRDTs. Each CRDT update carries a recursive
SNARK proof (o1js / Mina's Halo-Infinite PCD, citing Boneh-Drake-Fisch-Gabizon 2021) attesting that the
update satisfies an **application-defined validity predicate** `V`, *and* — by PCD recursion — that all
causal-predecessor updates satisfied `V` too. Verifying the carried proof is **O(1) in history size**; you
need **neither the full history nor coordination**. Two case studies: (a) a toy increment-counter with a
"divis-validity" invariant (`value mod id == 0` to increment), and (b) a Matrix-style HashDAG update-set CRDT
where the recursive predicate (their Eqns 1-4, refined to the streaming `V_I/V_B/V_R/V_f` recursion) attests
genesis-membership + predecessor-preimage-knowledge + `depth = max(pred depth)+1` + all-predecessors-valid.
Key engineering: a **fixed-size circuit over a variable number of predecessors**, achieved by recursing the
Poseidon Merkle-Damgård compression one predecessor at a time. Measured: ~30 KiB proofs, ~0.6 s verify,
but ~12 s/predecessor to *generate* — so they honestly scope it to **off-critical-path ops (GC, snapshot,
join/catch-up)**, not every update.

### The mapping onto dregg2
| dregg2 piece | their analog | relation |
|---|---|---|
| proof-carrying turn (`§1.2`, `§7`) | proof-carrying CRDT update | **same core move** — independent convergence |
| succinct non-interactive Byzantine validation | identical, verbatim their title | **same goal** |
| recursive/IVC backend (`§7`, `RecursionBackend`) | o1js / Mina Halo-Infinite PCD | **same family** — they ship the exact Pickles/Halo-accumulation interim impl `decisions §4` names |
| the CDT/blocklace as append-only partial order (`§1.1`) | the HashDAG / update-history poset | **same shape** (Fig. 1 = the CDT) |
| `ChainLink` conjunct (`§7.1`) | predecessor-preimage-knowledge + depth recursion | **same idea, narrower** (links only; no auth, no conservation) |
| I-confluence side-condition (`§2.3`) | "equivocation-tolerant validity: V must not depend on concurrent updates" | **same restriction, weaker statement** — see below |
| full `StepInv` incl. Conservation + Authority | — | **absent**; access-control "out of scope, important future work" |
| cross-cell ⊗ binding (CG-2 ⊗ CG-5, `§1.6`) | — | **absent** (single CRDT instance only) |
| coinductive soundness (`§1.3`, `Boundary.lean`) | — | **absent** (no metatheory; soundness = the PCD system's) |
| value-conservation rib (`§6.1`, Pedersen sum-to-zero) | — | **absent** |
| return-projection / zkRPC (`§6`) | — | **absent** |

### Verdict: CONFIRMED (independent convergence), with a narrow PARTIAL overlap. **NOT scooped.**
The headline idea — "apply PCD to CRDT updates for succinct non-interactive Byzantine update validation" —
is **literally, independently, theirs too.** That is the honest, slightly-uncomfortable finding: dregg2 cannot
claim the *bare* "proof-carrying Byzantine CRDT update" framing as unprecedented; a PaPoC '25 paper states it
in its title and ships an MIT-licensed o1js impl. **But** what they prove is a thin slice of dregg2's turn:

- **Their predicate is equivocation-tolerant-validity only.** Their explicit restriction — "update validity
  must not depend on concurrent updates" — is **exactly dregg2's I-confluence/tier-1 side-condition** (`§2.3`,
  `§2.2`: `I(x) ∧ I(y) ⇒ I(x ⊔ y)`), but stated as an *informal scoping assumption*, not a judgement, and with
  **no classifier** and **no metatheory**. dregg2's `Confluence.lean` (the `StateConstraint → I-confluent?`
  table, `STUDY-confluence-module`) is the thing that decides *which* predicates are PCD-attestable this way —
  they just assume the application author got it right. dregg2 still owns the *decidable classification* of the
  PCD-eligible fragment.
- **No authority in the proof.** They write, twice (Sec 4 end, Sec 7), that Matrix's access-control system is
  "out of scope … important future work." dregg2's **6-clause auth-in-proof** (`key → delegation →
  policy-entailment → effect-fold → replay → cell-root`, `§7.1`) is the single biggest thing dregg2 has that
  they don't, and the one they name as the open problem. **This is dregg2's clearest novelty island.**
- **No value-conservation.** Their counter increments by one; there is no notion of a conserved resource,
  no sum-to-zero, no mint/burn generators (`§2.1`). dregg2's "second rib" (per-class `CONSERVATION_VECTOR`
  folded into the same circuit, `§6.1`) is absent.
- **No cell/cap/coalgebra frame, no cross-cell binding, no coinductive soundness.** They have one CRDT, a
  validity predicate, and the PCD system's own soundness. dregg2's `StepInv` four-conjunct step-completeness,
  the `νC.µI` keystone, the equalizer/pullback CG-2⊗CG-5 cross-cell hypothesis (`§1.6`) — none of this exists
  in their work. They are not even adjacent to it.

### What dregg2 should BORROW (concrete, high-value):
1. **The fixed-size-circuit-over-variable-predecessors trick** (their `V_I/V_B/V_R/V_f` streaming recursion
   over Poseidon's Merkle-Damgård compress, one predecessor per step). This is **directly applicable to the
   `ChainLink` conjunct and the `graph-folding flat (non-recursive)` gap** flagged in `dregg2 §9` /
   `decisions §0.7`. Their construction is *exactly* how you make a per-turn proof bind a variable-arity
   predecessor set in-circuit without unrolling — i.e. it is a worked answer to the in-AIR-Merkle (M2) gap.
   It is also the constructive bridge from "depth-1 bounded-fan-in aggregation" (`decisions §6`) to true
   variable-fan-in chain attestation. **Adopt the streaming-compress predecessor recursion as the `ChainLink`
   circuit pattern.** `[G→F]`
2. **The honest perf scoping.** Their measured ~12 s/predecessor generation → "use PCD for ops off the
   critical path (GC, snapshot, join)" is a sober calibration dregg2's roadmap should inherit verbatim: the
   succinct-unbounded recursion (`§7`, `decisions §3`) is exactly a late-join/audit/teleport feature, **which
   is independent corroboration of `decisions §0.2`** ("recursion is a deferrable feature, not the soundness
   path"). They reached the same conclusion empirically.
3. **The o1js/Mina-Halo proof of life.** They built it on the *same* Pickles/Halo-Infinite-accumulation stack
   `decisions §4` picks as the ~80%-built interim `RecursionBackend`. This is external validation that the
   interim backend choice is real and ships. `[G]`
4. **The depth-as-causal-order trick** (`depth = max(pred depth)+1`, citing Schwarz-Mattern) as a cheap
   in-circuit causal-consistency check — pairs with `ObsAdvance`.

### What they have that threatens nothing but should be noted
Their soundness rests entirely on the PCD system being sound (heuristic Fiat-Shamir, o1js), and they cite the
o1js audit finding a real hash-padding collision bug (V-O1J-VUL-036) they had to patch. This is **live
corroboration of `decisions §0.7`/§4** ("the unaudited stack is the real risk; circuits silently under-constrain")
and of the SoK-SNARK-vuln checklist — a real-world instance of exactly the failure mode dregg2's adversarial
test checklist targets.

---

## 2. The two Byzantine-CRDT papers — do they move the I-confluence / blocklace story? `[G]`

### 2a. Extend-only Directed Posets (Jacob & Hartenstein, PaPoC '23)
**What it is:** a set-theoretic unification of DAG-based Byzantine-tolerant CRDTs (Matrix Event Graph,
blocklace, Kleppmann's BFT-CRDT transform) as **Extend-only Directed Posets (EDPs)** — append-only,
downward-directed posets whose join is set union, proven a CRDT under an *arbitrary number* of Byzantine
replicas (their Thm 1/2) **assuming a connected component of correct replicas + eventual delivery**.

**Effect on dregg2:** this is the **clean mathematical underpinning for `§1.1`'s "CDT ≡ strand log ≡ blocklace"
claim** and for the `finality.rs` Merkle-CRDT framing. Three concrete strengthenings:
- It proves the append-only partial order is a **join-semilattice with set-union join, Byzantine-tolerant
  without crypto in the state-based form** (crypto = an efficiency optimization, not a correctness requirement).
  This is the rigorous version of dregg2's "one DAG, join-semilattice CvRDT" assertion (`§2.2`) — **cite EDP as
  the precedent for the tier-1 substrate's semilattice structure.** It belongs next to the Gomes-Kleppmann and
  Baquero references in `Confluence.lean`'s precedent list.
- Its **finality property** for upward extensions — "once added, the downward closure of an element is fixed and
  cannot change" — is the formal statement of dregg2's append-only / monotone-attenuation CDT edge (`§1.1`) and
  of the `ChainLink` immutability the proof attests. The EDP "the upward closure is *never* final (a new upper
  element can always be in transit)" footnote is precisely why dregg2's revocation must be a *negative*
  discharge / non-membership proof (`§3`) and cannot be a positive append.
- Its **§3.2 systemic-access-control outlook** is the closest prior art to dregg2's CDT-as-authority idea: store
  policies/attributes *in* the CRDT, gain decentralized enforcement, and the rule "a concurrent administrative
  change is never *rejected* if authorized for its downward closure — it just might be *ignored* on
  linearization if another change wins." This is **a genuine sharpening of dregg2's authority model**: it
  separates *validity* (a Byzantine-safe, partition-tolerant, tier-1 judgement on the downward closure) from
  *effect* (a linearization/finality-tier judgement). dregg2 should adopt this split explicitly — it is the
  CRDT-native version of `§2.2`'s "commit at the join of written cells' tiers." **No threat; it confirms and
  refines.** dregg2's delta is that its authority edge is also *value-conserving* and *proof-carried*, which
  EDP access-control is not.

### 2b. Bounding Byzantine Impact in Open CRDTs (Albouy, Baquero, et al., PaPoC '26)
**What it is:** the observation that Byzantine-validity (papers above) bounds *what* an attacker can forge but
**not how much damage well-formed updates can do** (delete all text, `inc(10000)`, Sybil-spam `inc(1)`). Fix:
attach a **proof-of-work whose cost `C(op, pk, polog)` is proportional to the operation's semantic *impact***
(not raw count), with decentralized partition-tolerant adaptive difficulty over causally-closed views. Yields
a **bounded-impact property**: total adversarial impact ≤ f(budget B), independent of identity count → Sybil
resistance without consensus.

**Effect on dregg2 — this is the most genuinely-additive of the two, and it touches a real gap:**
- It identifies a class of attack **orthogonal to everything dregg2 currently models**: a tier-1 cell that is
  perfectly I-confluent, perfectly authorized, and perfectly conserving can still be *spam-griefed* by a
  Byzantine holder issuing unbounded well-formed updates. dregg2's `StateConstraint::RateLimit`/`RateLimitBySum`
  (`program.rs`, in the §1.5 catalog) is the *local* version; this paper gives the **open/permissionless,
  partition-tolerant, Sybil-resistant** version. Their `C(op,…) = impact` is exactly a generalization of
  dregg2's `RateLimitBySum`.
- **Sharpens the tier-1 eligibility story.** dregg2 says a cell is tier-1-eligible iff its merge is
  invariant-confluent (`§2.3`). This paper shows that **I-confluence is necessary but not sufficient for a
  *safe* open tier-1 deployment** — you also need impact-bounding, or a single griefer ruins availability for
  everyone while never violating any invariant. **Recommend: add an "open-deployment" annotation to the tier-1
  classifier** — a tier-1-eligible cell that is *open* (permissionless writers) must additionally carry an
  impact-cost function (PoW, or the paper's reputation/endorsement alternative). This is a real, missing
  side-condition, not a restatement. `[G→F]`
- Their **work-time / epoch / causally-closed-view** machinery (difficulty derived from PO-log content, no
  wall-clock) is a partition-tolerant, consensus-free metering primitive — directly relevant to the
  `coord/budget.rs` / computron metering that `dregg2 §10` files as "above core." It shows the metering can be
  **made Byzantine-safe and put *in* the data type**, which weakly argues that fee/rate economics is less
  cleanly-separable-from-core than `§10` claims for *open* cells.
- **No threat to I-confluence itself.** It explicitly assumes validity+convergence are handled (citing the EDP
  line) and bolts on orthogonally. It strengthens, doesn't threaten, the BEC side-condition.

**Net for §2:** neither paper changes the *blocklace/CDT framing* — they *are* that framing, made rigorous (EDP)
and made deployable in the open (impact-bounding). The I-confluence judgement is untouched as a judgement; what
changes is (a) it gains a clean semilattice precedent to cite, and (b) it gains a newly-identified companion
side-condition (impact-bound) for the *open/permissionless* tier-1 case.

---

## 3. Cambria — does it close the schema-DAG migration open problem (§5)? `[G]`

**What it is:** edit-lenses (Hofmann-Pierce-Wagner) applied to decentralized schema evolution, integrated with
the Automerge CRDT. Three pieces: (1) a bidirectional **edit-lens DSL** (add/remove, rename, hoist/plunge,
wrap/head, convert + higher-order in/map); (2) a **lens *graph*** — schemas are nodes, lenses are edges,
migration = traverse the shortest path, "concatenation of lenses is a lens"; (3) a **version-tagged CRDT** —
each op is tagged with its writer-schema, and on read each op is lens-translated to the reader-schema before
replay.

**Does it close the §5 DAG open problem? PARTIALLY — it gives the mechanism, not the theorem.**
- dregg2 `§5` proves migration transparency for the **linear chain** and flags the **fork/merge DAG case open**;
  `discoveries-2 §4` already names edit-lenses/Cambria as the tool. This paper **confirms that diagnosis exactly**
  and supplies the engineering substrate: the lens *graph* (not a list) is precisely the "schema-DAG" object,
  and "shortest-path lens composition" is the migration over a branching version history. **Adopt: model
  dregg2's schema migration as a lens graph over content-addressed `AIR-id` nodes** (`§5`'s `AIR-id =
  H(canonical(schema_decl))` *is* a Cambria graph node), with `migrate-on-read` = lens-translate-on-replay.
- **But it does NOT close the *theorem*.** Cambria is an experience report with **no transparency proof and no
  conservation guarantee**, and it is explicitly honest about the two gaps that are exactly dregg2's hard parts:
  - **§4.0.1 "irreconcilable design goals":** their three goals — **consistency / conservation / predictability**
    — *cannot all be satisfied* under a lossy lens (their assignee-delete example). dregg2's `§5` conservation
    obligation (`Σ before = Σ after + Σ dropped`) is dregg2's *answer* to their "conservation" goal, but Cambria
    shows the **round-trip law and conservation genuinely conflict for lossy lenses** — so dregg2's transparency
    theorem **must restrict to lenses where the dropped slot is non-linear, or emit a conservation witness for
    the drop.** Cambria proves this is a real constraint, not a corner case.
  - **§6.0.1 "CRDT semantics across lenses":** concurrent edits on two schemas related by a lens (their
    scalar↔array `wrap` example) can have **conflicting conflict-resolution strategies** that *break the
    consistency relation* — "we must align conflict resolution behavior across representations." This is the
    **DAG fork/merge case, and they leave it explicitly open.** So the precise sub-problem dregg2 `§5` flags
    open is *also open in Cambria* — Cambria does not close it.

**Concrete adopt:** (1) schema-DAG = lens-graph over `AIR-id` nodes, migrate-on-read = lens-translate-on-replay
(`§5`); (2) require lenses to satisfy the edit-lens round-trip laws **plus** a per-lens conservation side-obligation
(linear-slot drops emit the `Σ`-witness) — this is the dregg2-specific strengthening Cambria lacks; (3) take
their "store the lens-graph *in* the document" (self-describing migration) as the content-addressed,
gossip-friendly carrier — it matches dregg2's content-addressing discipline. **The DAG *theorem* (transparency
+ conservation + confluent-merge over a branching lens graph) remains dregg2's open problem; Cambria de-risks
the construction and confirms the two conflicting laws, but proves neither.**

---

## 4. Capability Policies (Drossopoulou & Noble, FTfJP '13) — does it sharpen the vat-boundary law? `[G]`

> Note: the file `the-need-for-capability-policies-drossopoulou.pdf` is the **2013 position paper** (Drossopoulou
> & Noble, "The Need for Capability Policies"), the precursor to the *Holistic Specifications* TOPLAS'21 paper
> (a separate PDF in the dir). It is a position paper — informal, no full logic — but it names the exact
> distinction dregg2's vat-boundary law rests on.

**What it is:** the argument that object-capability code tangles *policy* with *mechanism*, and we need explicit
**capability policies** with two ingredients:
- **Rely policies** (sufficient conditions): "executing `deposit` when both purses share a mint reaches a state
  where money transferred" — Hoare-style pre/post.
- **Deny policies** (necessary conditions): "the currency can change **only if** the code contained a call by
  the mint" (their Pol_2); "currency can **only grow**" (Pol_3). Deny policies are **pervasive** (span methods),
  **persistent** (compare state across *time* — need temporal/modal operators `□`, `◇`-prev), and **implicit**
  (depend on the whole heap, e.g. currency = sum of all purse balances — a *conservation* quantity).

**Does it sharpen dregg2's vat-boundary law / de-jure-vs-de-facto split? YES, and quite precisely. `[G]`**
This is the cleanest conceptual gift of the five. The **rely/deny split is the missing vocabulary for dregg2's
`BA`-vs-`TP` (de-jure-permission vs de-facto-authority) split** (`§0`, `Positional.lean`):
- A **rely policy is a de-jure statement** — "a legal derivation path existed ⇒ this transition is permitted."
  This is exactly what dregg2's badge attests (`§6b`: "(permitted) ∧ (effects-as-committed)").
- A **deny policy is a de-facto statement** — "the currency changed ⇒ the mint must have acted." It is a
  *necessary-condition / what-can-eventually-be-caused* claim, recovered by reasoning over the **history of
  execution**, which is **exactly dregg2's "de-facto authority recovered behaviorally from the log, never from
  the badge"** (`§0`, `§6b`). The paper independently arrives at dregg2's central honesty: **the badge can carry
  the rely (de-jure) half but the deny (de-facto) half is a property of the whole execution history.** That is
  strong, independent confirmation that the split is real and load-bearing, not a hedge.
- Their **Pol_2/Pol_3 are dregg2's conservation law in policy form**: "only the mint can violate conservation"
  (Pol_2) = dregg2's `mint/burn are the only typed generators that move `Σ_k`" (`§2.1`); "currency can only grow"
  (Pol_3) = a monotonicity invariant. The paper frames conservation as a **deny policy over an implicit
  whole-heap quantity** — which tells dregg2 that the conservation conjunct is, formally, a **deny-style temporal
  invariant**, and the natural home to *state* it is the coinductive `Boundary.lean` (over the history/`▶`-chain),
  **not** a per-method Hoare pre/post. This corroborates `decisions §2`'s "state conservation coinductively, not
  inductively over `List Turn`."
- Their suggested tools — **ownership types** for "no one affects a purse they don't have" (Pol_4) and **effect
  systems** for "purses of different mints don't interact" (`m ≠ m' → m.Purse() # m'.Purse()`) — are the
  positional-authority and conservation-disjointness analogs dregg2 realizes as the l4v integrity case-split
  (`Positional.lean`) and the per-asset `LinearityClass` separation (`§6.1`). dregg2 *implements in a proof* what
  they *specify in a logic*.

**Concrete adopt:** (1) **rename/frame the badge contract using rely/deny** in `§6b` and `Positional.lean` — the
badge attests the **rely** half; **deny** properties (de-facto authority, conservation-over-history, "currency
only grows") are **whole-history coinductive invariants** discharged in `Boundary.lean`, not on the badge. This is
free vocabulary that makes the §0 honesty note rigorous. (2) Their "deny policies need modal `□`/`◇`-prev over
program *state* (not events)" is the precise argument for why dregg2's soundness statement must be the
`▶`-guarded coinductive bisimulation over the receipt-chain — **independent grounding for `decisions §2` /
`Boundary.lean`.** No threat; it is a vocabulary and a justification, both confirming.

---

## 5. Net novelty calibration (honest, one paragraph)

After these five, dregg2's novelty map sharpens but does not collapse. The **bare framing** "proof-carrying
Byzantine-CRDT update, succinct + non-interactive, via recursive SNARK/PCD over an append-only partial order"
is **NOT novel** — Marx/Jacob/Hartenstein published it (PaPoC '25, with a shipping o1js impl), and the EDP and
impact-bounding papers are the rigorous CRDT substrate it sits on; dregg2 must stop implying that *combination*
is unprecedented. What **remains genuinely dregg2's** is the *content of the attested predicate and the frame
around it*: the **full step-complete `StepInv`** — and specifically the **6-clause authority-in-proof** (which
the PCD-CRDT paper names as its #1 open problem), the **per-asset value-conservation rib folded into the same
circuit** (absent everywhere), and the **coinductive soundness statement** (`νC.µI` + `▶`-guard) that makes the
whole thing a bisimulation rather than a per-update predicate check. Also genuinely dregg2's, and *un-scooped*:
the **cross-cell ⊗ binding** (CG-2 ⊗ CG-5 equalizer/pullback — every paper here is single-instance), the
**caps↔keys lossy boundary functor** with its named Property-E/F loss, the **decidable tier-eligibility
classifier** (the papers *assume* their predicate is equivocation-tolerant; dregg2 *decides* it), and the
**unified VERIFY/FIND seam** across auth/intent/ordering/migration. The honest residue: dregg2 is best
described as **a novel *synthesis with three genuinely-new load-bearing pieces*** — auth-in-proof, the
conservation rib, and the coinductive step-complete frame — **assembled on a substrate (PCD-over-CRDT, EDP
semilattice, edit-lens migration, rely/deny capability policy) that the literature already supplies and, in
the PCD-CRDT case, has independently built the skeleton of.** The right posture is confidence, not alarm:
the scariest possible paper (the on-the-nose PaPoC '25 one) turned out to **confirm the direction and hand
dregg2 a reusable circuit trick (streaming-compress predecessor recursion)**, while explicitly leaving
dregg2's hardest claims (authority-in-proof, conservation, the full step) as *its own* stated future work.
