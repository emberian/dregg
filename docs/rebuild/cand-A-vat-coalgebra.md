# Candidate A — dregg2 as a Network of Live Coinductive Cells (the Vat-Coalgebra OS)

> **What this is.** ONE candidate whole-system architecture for **dregg2 = Robigalia**:
> seL4's capability discipline pushed across an untrusted global network into a *persistent,
> distributed operating system* where developers collaborate on untrusted code without their
> machine getting hacked, with checkpoint / restore / replay / time-travel / advanced debugging
> as *native consequences* of the design rather than bolt-ons.
>
> **The center (non-negotiable for this candidate):** a cell is **live CODATA** — an element of a
> final coalgebra. The system is a network of persistent coinductive processes (vats hosting
> cells). Everything else — caps, turns, proofs, finality — is read through that lens. This is
> the *coinduction-first* reading of the corrected canon in `00-synthesis.md`, `pdfs/discoveries.md`,
> `pdfs/decisions.md`, and the three spine docs. Where those docs left two co-primary primitives
> (cell + morphism) sitting awkwardly side by side, **the coalgebra unifies them**: the morphism
> is the transition *structure* of the object, not a second object.
>
> This doc holds the detail. The orchestrator gets a ≤250-word abstract; everything load-bearing
> is here.

---

## 0. The thesis in one breath

A blockchain is a *ledger of transactions* — an inductive list you fold to get a state. **dregg2
is not that.** dregg2 is a *living OS of processes*: each cell is a non-terminating reactive
object that, forever, observes-then-awaits-the-next-admissible-turn. The right mathematics for
"a thing defined by how it *behaves over unbounded time*, not by how it was *built up from a
base case*" is **codata / final coalgebra / coinduction**. That single choice is what makes
dregg2 *an operating system* and not a chain:

- a **process** is codata (a stream of observations under a transition function), not a value;
- **soundness** is a *bisimulation* (two cells are "the same" iff they behave the same forever),
  not a structural-induction proof over a transaction list;
- **checkpoint / restore / replay / time-travel / debugger** are not features — they are *what
  you can already do* with codata + a retained input log + a rollback-handler turn;
- **liveness across an untrusted network** is the coinductive guard (`▶` "later") being
  *productive*: each step emits one observation now and defers the rest, so the process never
  has to "finish" to be sound.

The corrected system-wide law — **VERIFY is tractable, FIND is intractable; TCB = the verifier;
soundness-by-verification** — is the *operational engine* of this coalgebra: the transition
function `AdmissibleTurn ⇒ X` is gated by a checkable witness, never by a trusted search.

---

## 1. The core ontology (the final coalgebra)

### 1.1 The functor

```
F X = Obs × (AdmissibleTurn ⇒ X)
```

A cell is an element of the **final coalgebra `νF`**: a thing that, when observed, yields a
current observation `Obs` together with a function taking each *admissible* turn to its successor
cell. This is precisely a **Moore machine / DFA coalgebra** (output-on-state, transition-on-input)
— and the DFA shape *is Robigalia's* design, lifted from a single kernel to a global network of
persistent objects.

Read each piece against the canon:

- **`Obs`** = the *attested, externally-visible projection* of the cell — its committed head, its
  public `FieldVisibility` fields, its lifecycle phase, its facet (the interface it exposes). `Obs`
  is what crosses a vat boundary; it is the "badge." Critically, **`Obs` must be monotone** in the
  sense that the soundness clause `ObsAdvance` demands: each turn advances the observation along the
  receipt chain, never silently rewinds it.
- **`AdmissibleTurn`** = the *dependent* input alphabet. Not every turn is admissible from every
  state; admissibility is exactly **step-completeness** (§4): a turn is admissible iff it carries a
  witness discharging `Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`. The `⇒` is therefore a
  *partial, witness-guarded* transition, and **this is where the verifier (the TCB) lives**.
- **`⇒ X`** = the successor cell — *again codata*. A cell does not transition to a "final state";
  it transitions to another live cell. There is no base case in the outer structure. That is the
  whole point: an OS process does not terminate to be correct.

### 1.2 Why coalgebra and not algebra (and why this is distinctly dregg)

The three spine docs landed on "two co-primary primitives, cell + morphism, and don't collapse
logs/relations into cells." The coalgebra **dissolves that tension correctly** instead of
papering it:

- A **cell** is the *carrier* of the coalgebra (a point of `νF`).
- A **turn** is the *transition edge* `X → X` *inside* `F` — it is not a second kind of object, it
  is the action of the structure map `c : X → F X`. The cell-spine's worry ("a morphism is
  first-class too, so we secretly have two primitives") is answered: in a coalgebra the morphism
  *is* the object's behavior. One primitive, two faces.
- A **strand / log** is the *trace* of the coalgebra — the sequence of `(Obs, turn)` pairs you get
  by unfolding `c`. The cell-spine was right that "a log is an order, not a state, don't objectify
  it." In the coalgebra the log is *neither* a state nor a separate object: it is the **anamorphism
  image** (the unfold) of the cell. It comes for free and is correctly typed as a *path*, not a
  *point*. This is the single cleanest payoff of going coinductive.

**The algebra/coalgebra duality maps the whole canon:**

| Inductive (algebra, "a chain") | Coinductive (coalgebra, "an OS") |
|---|---|
| state = `fold` over a `List Turn` | state = `Obs` of the current `νF` point |
| a transaction is consumed | a turn is *observed*, the process continues |
| termination = correctness | productivity (`▶`-guarded) = correctness |
| base case = genesis fold seed | base case is *inside* the per-turn proof (the inner-µ), not the cell |
| history is reconstructed by replay-from-zero | history is the retained unfold; replay is *resuming an unfold* |

### 1.3 The two ribs the coalgebra carries but does not *own*

The canon is emphatic (cap-spine §7.1, §8.b; discoveries §3.2): **conservation** and **ordering**
are not authority and not reducible to a single primitive. The coalgebra honors this by making them
*ambient laws on the transition*, not fields of the object:

- **Rib 1 — Conservation (the "second rib," folded INTO the proof per-asset).** `Σ_k` is a **strong
  monoidal functor** `(TurnCat, ⊗, I) → (ℕ, +, 0)`, constant on every non-mint/burn hom-set
  (discoveries §3.2). In the coalgebra this is a side-condition on `AdmissibleTurn`: a turn is
  admissible only if, *per linear asset class k*, the witnessed effect stream sums to zero (mint/burn
  are explicit typed generators). The validated gap from the brief — *value-conservation must be
  folded into the proof per-asset, not checked as one aggregate scalar* — is here a **per-class
  `CONSERVATION_VECTOR`** clause inside step-completeness, not a single `net_delta`. Conservation is
  the withholding of the cartesian copy `Δ` and erase `◇` maps (Selinger / Girard); the system is a
  **symmetric-monoidal** category, *thin only in its ordering fragment* — never a "thin posetal"
  category (that cannot carry Law 1's symmetry iso).

- **Rib 2 — Ordering / canonicity (which valid history is *the* history).** The proof-spine's
  honest verdict (§10–11): a proof certifies *validity*, never *canonicity*. The coalgebra inherits
  this exactly — `νF` tells you a cell *can* take turn A and *can* take turn B from the same state;
  it does not say which fork is canonical. Canonicity is the **pluggable finality menu** (§7), a
  *separate* coupled structure. Per **I-confluence** well-formedness (discoveries §3 item 7): a cell
  may select tier-1 (causal-only) ordering **only if** its state is a bounded join-semilattice with
  invariant-preserving joins (`I(x) ∧ I(y) ⇒ I(x ⊔ y)`). The corner *tier-1 + non-I-confluent
  invariant* is **a static type error**, not a runtime concern. `balance≥0` is not I-confluent
  (needs ≥ tier-2 or single-owner); hash-keyed nullifier uniqueness is.

---

## 2. How cell / turn / cap / proof look under this lens

### 2.1 The cell — `νF` point, hosted in a vat

```
Cell = νC. µI. StepProof I × (Turn ⇒ C)
```

This is the keystone type (decisions §2; discoveries §5). Read it outside-in:

- **outer `νC`** = the unbounded life of the cell (coinductive; never bottoms out).
- **inner `µI`** = the *bounded* per-turn proof (inductive; a finite obligation tree —
  Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance, depth-1 bounded-fan-in aggregation, the
  inductive inner-µ of decisions §6).
- **`StepProof I`** = the step-complete witness for *this* turn.
- **`Turn ⇒ C`** = the guarded successor — and the guard is `▶`.

The cell's *substrate footprint* is `(id, head, rule)` + its retained input log (the unfold). The
materialized bytes are a cache of `head`'s preimage; the **log is the truth, the DB is the cache**
(houyhnhnm orthogonal persistence). A cell is *reconstructible by resuming its unfold* from any
retained checkpoint — which is exactly §5's checkpoint/restore.

A **vat** is the host of one or more cells and *is the trust-root boundary* (not "membrane" —
discoveries §2a; "membrane" is reserved for Miller's revocable-forwarder pattern). "I trust my
MacBook" / an seL4 CSpace = one vat. Inside a vat, authority is **positional / caps-as-caps**
(a mediator slot-read, the kernel or a live session enforces it); across vats, authority is
**epistemic / keys-as-caps** (a freely-copyable, verifier-checkable witness). The caps→keys
forgetful functor Φ drops *exactly* Miller's Property F (confinement) + Property E (revocable
forwarders) — a **named, exact loss**, not a slogan (discoveries §2b). Φ⁻¹ needs a trusted minter.

### 2.2 The turn — the coalgebra step *and* the rollback handler

The brief's sharpest unification: **a turn IS the rollback handler** (discoveries §3 item 5;
Plotkin-Power §6.8). A turn is a transaction whose outgoing effects are *held until it commits*:

- **commit** = replay the held effect log → advance the unfold by one `▶` step → (at a vat
  boundary) emit the witness.
- **abort** = discard the held log = *conservation-preserving refund* (the linear resources were
  never released).

Continuations are the *one* effect that is **not** algebraic (Plotkin-Power), so the turn is NOT
"the free model of await." The await substrate is **two layers**: a gate-engine (algebraic handler)
+ a delimited-continuation capture primitive. The turn-as-rollback-handler carries the
held-until-commit list verbatim, and **the deferred-prover keystone is: the commit-replay handler
also emits the witness at the vat boundary.** This is the single mechanism behind both rollback and
proof-on-export.

**Turn is one-directional → the return projection (the validated second gap).** The brief flags
that a turn going *out* needs a way for a result to come *back*. The coalgebra makes this precise:
a forward turn is the structure map step `c : X → F X`; the **return** is a *second observation* the
caller awaits — modeled as the `Await` face (§3) plus a **"settled-call" await-face**: the caller
suspends on a predicate "the callee's `Obs` has advanced past receipt R," and resumes when that
observation is witnessed. The agent / zkRPC product is therefore: forward turn (one-directional)
+ **return projection** (a typed `Obs`-delta the callee commits) + **settled-call await** (the
caller's resumption gate). zkRPC = a turn whose return projection is a proof-carrying `Obs`.

### 2.3 The cap — an unforgeable edge in the admissible-transition relation

A capability is *the thing that makes a particular turn admissible*. Under the coalgebra it is an
edge-label on `AdmissibleTurn ⇒ X`: holding cap `c` means "the turn that exercises `c` is in the
admissible alphabet from this state." Concretely a cap is a **CDT node**
(`{root, target, authority, facet, caveats, parent, delta}`, content-addressed by `CapHash`),
and the admissibility witness is a **derivation proof**: a path in the CDT from an unforgeable root
to the exercised node, every edge a monotone attenuation, every caveat discharged.

But honor the corrected nuance (discoveries §3 item 6, the BA-vs-TP correction): **the CDT proves
*permission* (de-jure), not *authority* (de-facto).** A caretaker/forwarder makes the static
cap-graph *lie* about what a cell can eventually do. So the cap edge attests "you were *permitted*
to take this turn"; what the cell can *behaviorally* reach is recovered from the log (BA). **Truth
is the log; the cap-graph is a permission certificate.** This is why the coalgebra puts the cap on
the *transition guard* and the behavior in the *unfold* — they are different things.

seL4 reflection: a `RootSeal::Sel4Reflected` edge needs *no* derivation proof for intra-vat
exercise (the kernel IS the proof — positional authority); it acquires a derivation proof only when
it crosses a vat boundary (keys-as-caps). `badge ↔ CapHash` is the slot-handle duality at the
kernel layer.

### 2.4 The proof — `StepProof`, the admissibility witness, PCA+IVC auth-in-proof

The per-turn `StepProof` is the **step-complete** statement (§4). Authorization lives **in the
proof** (PCA: "authorization = a proof in a logic the verifier checks, not an ACL"): the 6-clause
auth-in-proof statement — key → delegation → policy-entailment → effect-fold → replay → cell-root
binding (cross-PI-bound) — turns an effect-transition proof into a *turn* proof. The PI surface
*is* the entire trust boundary: `AIR_VERSION, OLD/NEW_COMMIT, EFFECTS_HASH (re-derived in-circuit),
AUTH_ROOT, ACTION_AUTHORITY_DIGEST, CONSERVATION_VECTOR (per-class), TURN_HASH/ACTOR_NONCE/
PREVIOUS_RECEIPT_HASH, CONSTRAINT_MANIFEST_HASH`.

**The no-unconditional-IVC bound:** there is *no* arbitrary-depth / NP-witness IVC for free —
**depth = security parameter** (decisions §0.2, §4). Recursion (succinct-unbounded history for
teleport/late-join/audit) is a *deferrable feature*, **not** on the soundness-critical path, and
lives behind ONE swappable `RecursionBackend` trait (`MAX_DEPTH: Option`, `needs_cycle: bool`;
**never** an `additive_combine` method — that forks into two IVC layers). The leaf prover stays
FRI/BabyBear/Poseidon2 (already PQ/hash-native); the recursion layer's PQ-ness is the deferred swap
(lattice-IVsC target, ~80%-built Pickles/IPA Halo-accumulation interim).

**Identity by content-hash (Preserves):** cell-state = name-keyed `Record @schema #"air-id"`; facet
= canonical **Set of effect Symbols** (adding `transfer` adds an *element*, never shifts a bit —
kills `EffectMask` bit-fragility); `AIR-id = H(canonical(schema_decl))` (kills frozen-AIR). Schema
upgrade = lazy `migrate-on-read`, sound iff **transparent** (commitment-equality) **AND
conservative** (linear-drop emits `Σ before = Σ after + Σ dropped`).

---

## 3. The await family — one continuation primitive, four faces, plus the return face

A suspended morphism awaiting a predicate-satisfying resolution. **One** `Await`/`Resolver`
inductive (`named | gateway | exists P | registry`), one-shot (linear) continuation typing, so
conservation falls out as a corollary (Dolan's "raise on 2nd continue" becomes *derivable*).
Multi-shot is sound only for `Copy`/non-conserved payloads.

| Face | Resolver | Direction |
|---|---|---|
| zkpromise / zkawait | specified party | forward, point-to-point |
| discharge (3rd-party caveat) | named gateway | forward, the `Await` *engine* of the universal gate |
| intent | *any* filler satisfying P (∃) | the **inverse** vat boundary: gates the *missing half* |
| **settled-call return** | the callee's advanced `Obs` | **backward** — the return projection (§2.2) |

Intent is the inverse boundary: a vat boundary gates a *complete* turn crossing out; an intent gates
the *filler* crossing in (`λ(fill satisfying P). effects`). The **VERIFY/FIND seam** is sharpest
here: VERIFY a claimed fill = tractable (the universal gate); FIND a fill = undecidable in general
(HOU-undecidable, machine-checked in Coq). So the matcher is a **bounded, pluggable, untrusted
plugin emitting a checkable witness** — `no_general_matcher` via `HOU ⪯ GeneralMatch`; the plugin
contract requires *soundness-by-verification only* (completeness/termination explicitly NOT
required). Winner-determination is NP-hard, no PTAS — a plugin may promise only tractable structured
cases.

---

## 4. Step-completeness — the soundness-critical path (and the drifting-future risk)

`StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`. **This — not recursion — is the
soundness question** (decisions §0–2). Soundness = a **▶-guarded bisimulation** carrying `StepInv`
to the Lean golden-oracle Spec, holding **iff each step attests the *complete* `StepInv`**.

- **Conservation** — per-class `Σ_k` invariance (Rib 1).
- **Authority** — the 6-clause PCA chain (de-jure permission).
- **ChainLink** — `previous_receipt_hash` = Birkedal's `▶` ("later"): head now, tail later →
  productive, uniquely-solved corecursion. This is the guard.
- **ObsAdvance** — the observation moves forward along the chain (no silent rewind).

**The drifting-future failure mode (the central risk of going coinductive).** A *step-incomplete*
proof is worse here than in an inductive system. In an inductive list, a bad step is a bounded local
error. Under coinduction, a **non-contractive step** — one that locally type-checks while slowly
leaking `Σ_k` — has *unbounded* consequence: the chain corecurses forever, drifting, each step
individually "fine." A cell can pass every per-turn check and still bleed value to infinity. **The
guard `▶` only buys productivity, not soundness; soundness needs the step to be *contractive* in
`StepInv`.** Therefore the **highest-priority audit** is: *is the live AIR actually step-complete —
all four conjuncts in-circuit?* If not (memory flags: intent-predicates unenforced, graph-folding
flat, auth-checked-outside-the-proof), **the bisimulation does not hold and nothing downstream is
sound — and the fix is step-completion, not more recursion.**

---

## 5. Checkpoint / restore / replay / time-travel / debugger — NATIVE, not bolted on

This is where the codata choice pays for itself. Each capability is a *direct consequence* of
(codata + retained log + rollback-handler turn), with **zero new machinery**:

- **Checkpoint** = *name a point in the unfold*. A cell's substrate footprint is already
  `(id, head, rule)`; a checkpoint is just a retained `(head, receipt)` pair. No snapshot subsystem
  — the coinductive head IS the checkpoint. (Cap-spine `DelegationMode::SnapshotRefresh` was the
  embryo.)
- **Restore** = *resume the unfold from a retained head*. Because the cell is codata, "going back"
  is not undoing — it is **re-seeding the anamorphism** at an earlier point. The retained log
  guarantees the resumed unfold is bit-identical (the proof attests faithful replay).
- **Replay** = *re-run the unfold from the log* (houyhnhnm "the log IS the inputs"). The DB is a
  cache; the log is truth; replay re-derives the cache. Differential against the Lean oracle for
  free (decisions §9).
- **Time-travel** = *fork the unfold at a checkpoint and run an alternate admissible-turn stream*.
  This is **literally `Fork`** (§6): one pre-state, two valid descendant heads. Time-travel debugging
  ("what if I'd taken turn B instead of A at step 7") is a fork at step 7 — already a first-class
  operation, governed by the same attenuation-validity merge rule.
- **Advanced debugger** = *step the coalgebra under operator control*, inspecting `Obs` at each `▶`.
  Because the turn is the rollback handler, the debugger's "step back" is `abort` (discard held
  effects, conservation-preserving); "step forward" is `commit` (replay + advance). **Breakpoints
  are admissibility predicates**: "suspend before any turn whose `ACTION_AUTHORITY_DIGEST` touches
  cell C." The debugger is not instrumentation over the runtime — it *is* the runtime's own
  rollback-handler exposed to an operator. A failed proof, normally an opaque STARK "no," becomes
  inspectable: the debugger replays the witness build and shows *which conjunct of `StepInv`*
  rejected (mitigating proof-spine §10.7 opacity).

**The Robigalia developer-collaboration story (the actual vision).** A developer pulls an untrusted
project and runs it *as cells in a sandbox vat on their machine*. The vat is the trust-root
boundary: the untrusted code holds only the caps explicitly delegated into its CSpace (positional,
kernel-enforced intra-vat). Nothing it does can affect the host's other cells without a turn
crossing the vat boundary — and *every* boundary-crossing turn is step-complete-witnessed
(keys-as-caps, verifier-checked). If the untrusted code misbehaves, the developer **time-travels**
to before the bad turn, inspects via the debugger which `StepInv` conjunct it tried to violate, and
**forks** an alternate history. Persistence means the sandbox survives reboot (orthogonal
persistence: the log is the inputs). This is "how far can seL4's capability discipline extend across
an untrusted global network" answered concretely: *as far as the verifier (TCB) can check a witness,
which is everywhere, because VERIFY is tractable.*

---

## 6. Fork / merge — the one hole, defined coinductively

Fork is *free* in a coalgebra: anyone can extend any verified head; forking yields two valid
descendant heads of one pre-state (`Obs` branches). **Both are valid as morphisms; neither is
canonical** (proof-spine §10.4 — the deepest crack, inherited honestly). Canonicity is the finality
menu (§7), *not* the proof.

**Merge** = re-root the fork's sub-unfold under the (possibly-advanced) parent, legal **iff every
edge stays a monotone attenuation** (cap-spine §4.2) **and** linear conservation holds across the
fork: `Σ consumed across both branches ≤ Σ available at the fork point`. For I-confluent (lattice)
state, merge is the CRDT join (sheaf glue). For linear/non-I-confluent state, merge must *pick* or
prove a split — and **provably fails** on a genuine double-spend, which is correct. Fork is **not a
categorical coproduct** (that re-imports cocartesian merge-for-free, which resource categories lack);
it is a chosen span/pushout with hand-proved laws (discoveries §3 item 3). Recipe serialization is
capability-sealed: a forked/teleported cell must not serialize authority it never held.

---

## 7. Finality — the pluggable ordering rib (Law 2), coupled but separate

One DAG (a join-semilattice CvRDT — *proven*, Merkle-CRDT); pluggable finality on top (Narwhal/
Mysticeti-validated: separate dissemination from ordering). `τ_unified(B, G, C)` runs τ *per
reference-group*; `C` selects the **finality rule**; `½(n+f)` → group config.

| Tier | mechanism | n | synchrony | partition |
|---|---|---|---|---|
| 1 Causal-only / CRDT | add block; causal order | 1+ | none | **never blocks** (phones over BLE keep working) |
| 2 Ack-threshold | k-of-m acks, no leader | small | none for safety | degrades to tier 1 |
| 3 Cordial-Miners τ-BFT | waves + leader + 3-step | known Π, n≥3 | GST/async | **stalls**, resumes after GST |
| 4 Constitutional | τ-BFT + self-amending (P,σ,Δ) | known P, PKI | partial-sync | stalls + deadline |

A block written under tier 1 can be finalized under tier 3 later (liquid→solid crystallization).
**`FinalityRule.admits(invariants, actions)` runs the I-confluence check as a soundness gate**; a
cell-state-lattice requirement is the tier-1 eligibility criterion; cross-tier rule: *a turn commits
at the **join** of its written cells' tiers; effects held until the join-tier commits; no finalized
value downgrades; conservation is tier-independent and only prunes the order search.* Adopt
constitutional *amendment rules* as the tier-4 plugin; **reject** its four globalism seams (single
global total order; GST-as-precondition-for-any-progress; fixed σ-quorum forbidding n=1;
synchronized wall-clock deadline). Heads summarized **by hash, not vector-clock counters** (BEC §4.2
forgeability — a live soundness check, not a musing).

---

## 8. The metatheory entry-point

A **coinductive Core** (Lean4, `./metatheory`), stated coinductively from day 1 — *not* inductively
over `List Turn` (decisions §2):

- `TurnCoalg` — the structure map `c : X → F X`.
- coinductive `Sound` / `IsBisim` — soundness as a ▶-guarded bisimulation to the golden-oracle Spec.
- `theorem sound_of_step_complete` — **the keystone**: `(∀ step, StepComplete step) → Sound c`. This
  is the formal content of §4: contractivity in `StepInv` ⇒ no drifting future.
- `conservation_comp` — `Σ_k` is a strong monoidal functor to `(ℕ,+,0)`, constant off mint/burn.
- the **vat-boundary law** (LAST, the sharpest): two theorems — *intra-vat* admits the trivial
  positional witness (`∃ cap ∈ caps`); *cross-vat* admissibility ⇔ `Discharged P w`
  (`Verify P w = true`). The crypto substitution is *literally replacing the positional ∃ with the
  decidable verification*. Companion: a `LossyMorphism` theorem stating caps→keys loss =
  revocation-by-construction. **Template to copy: the l4v integrity theorem** (`~/dev/l4v`,
  Isabelle) — the single most load-bearing unread artifact; read before writing `Authority/`.

Mathlib: `MonoidalCategory` + `SymmetricCategory` (Law 1); `Preorder.smallCategory` (thin ordering
fragment, Law 2); `GaloisConnection` + `HeytingAlgebra` (`Predicate ⊣ Witness`, the cheap posetal
form — *not* a heavy `Adjunction`). The Lean `def … deriving DecidableEq/Repr` is *simultaneously*
the proof target and a runnable `Verify P w : Bool` — wired as backend #8 of the
`dregg-dsl-differential` harness (Lean = golden oracle). **Crypto soundness (the STARK attests the
morphism) is a *circuit* obligation — NEVER merged into the Lean law** (the §8 README caveat).
Iris is overkill for the skeleton; reserve it for the one concurrent-live-session interior obligation
(`CapSession`).

---

## 9. Honest tradeoffs / risks (ranked)

1. **Step-completeness is unverified today (FATAL if true).** The bisimulation — hence all of
   §4–§5 — holds *only if* the live AIR attests all four `StepInv` conjuncts in-circuit. Memory
   flags it does not (intent-predicates unenforced, graph-folding flat, auth-outside-proof). **This
   is the single highest-priority audit; the fix is step-completion, not recursion.**
2. **The drifting-future mode (§4).** A non-contractive step leaks `Σ_k` *unboundedly* under
   coinduction. The coalgebra is *less* forgiving of a partial proof than a chain would be. The
   mitigation (per-class conservation folded in-proof, the contractivity theorem) is the price of
   admission for going coinductive — and it is non-negotiable.
3. **Proof cost vs. interactivity (proof-spine §10.1–10.2).** Auth-in-circuit + effects-fold +
   per-cell rules is heavy (tens of seconds to minutes on a phone for a deep chain). Asymmetric
   prove/verify saves the *verify* side (gossip a strand head, verify in ms); but any speculative
   "ahead-of-proof" cache holds un-proven state. Defensible stance: provisional state is allowed but
   **never gossiped and never authorizes a downstream turn until proved** — proof is truth *at every
   boundary crossing*, not every keystroke. This re-frames the brief's "live-session-then-attest"
   decision precisely.
4. **Canonicity is not in the proof (proof-spine §10.4–10.6).** Fork/genesis/turn-identity all
   reduce to "which valid history is *the* one" — an ordering question. The coalgebra is *honest*
   about this (it's the §7 rib), but the brief must not let the coinductive elegance pretend to
   subsume ordering. Two coupled spines: codata for validity, finality for canonicity.
5. **Genesis / bootstrapping.** Strand-IVC proves "valid chain from genesis"; *nothing* proves
   genesis. The ground turtle is either a trusted setup or a consensus act or an seL4-reflected root
   (the Robigalia answer: genesis authority bottoms out in the kernel cap — coherent, but it means
   the trust base for a fresh cell is the *host vat*, not the proof). Document the residue.
6. **caps→keys is lossy in a named direction (discoveries §2b).** Cross-vat, you lose confinement +
   cheap revocation + live interposition. Prefer **short expiry + renewal over revocation**;
   revocation is a tombstone edge reaching finality at the tier's pace, with a known-uncertain
   window the receipt records (for detect-and-compensate, not prevent). Any design claiming clean
   global revocation under local-first is lying.
7. **seL4 lattice-alignment tax (cap-spine §7.6).** dregg's rich facet/caveat set has no kernel
   counterpart; dregg→kernel is a *partial functor*, not an isomorphism. The caveat-rich part lives
   in a user-space Robigalia shim the kernel cap gates. Document the non-reflected residue.

---

## 10. What is distinctly dregg2 here (not a paper re-impl)

- **The OS *is* the final coalgebra.** Not "we use coinduction to model a chain" — the *primary
  object of the system is codata*. A cell is a living process, the network is a population of them,
  and "transaction ledger" is a *projection* (the unfold trace), not the substrate. No prior
  capability OS and no prior blockchain takes `νF` as the literal system primitive.
- **Checkpoint/restore/replay/time-travel/debugger are theorems, not features.** They are the
  *definitional consequences* of (codata + retained log + rollback-handler turn). A paper re-impl
  would add a snapshot subsystem; here there is nothing to add — the coinductive head *is* the
  checkpoint, fork *is* time-travel, the rollback handler *is* the debugger's step engine.
- **The turn is simultaneously the coalgebra step, the rollback handler, the conservation refund,
  and the deferred-prover trigger.** Four roles the canon found scattered, unified by one
  observation: commit = replay-the-held-log + advance-the-`▶` + emit-the-witness.
- **Soundness is a bisimulation with a named failure mode.** The "drifting future" of a
  non-contractive step is a risk *only a coinductive system has* — and naming it, then discharging
  it with `sound_of_step_complete`, is the metatheory's distinctive contribution. l4.verified
  certified a *kernel*; dregg2's Core certifies a *distributed coinductive OS's step law*.
- **VERIFY-tractable / FIND-intractable as the OS's scheduling law.** Every search (match a fill,
  find a delegation path, find an ordering, find a handler) is an *untrusted plugin emitting a
  checkable witness*; the kernel (TCB) only ever *verifies*. This is what lets the OS extend across
  an *untrusted* global network at all — the property no single-machine capability OS needed and no
  ledger framed this sharply.
- **Two coupled spines, honestly.** Codata-for-validity + finality-for-canonicity, with conservation
  and ordering as ribs the coalgebra carries but does not own. The candidate's strength is that it
  *refuses* the totalizing slogan ("everything is a cell" / "proof is truth" / "everything is a
  cap") that each spine doc independently warned against — and instead makes the *coalgebra* the one
  thing that legitimately unifies cell-and-morphism, while leaving the two ribs exactly where they
  belong.
```

---

## 11. The keys-as-caps token layer — how a vat EXPORTS c-list authority

The keys-as-caps axioms (the vat-boundary law, `discoveries.md §4–5`) are abstract until the
**concrete token layer** places them. `Authorization::Token { encoded, key_ref, discharges }` +
`TokenKeyRef` (`turn/src/action.rs:422–450`) *is* the mechanism by which a vat's c-list authority
becomes a transmissible object on exit. The split is the membrane itself:

- **biscuit** (`eb2_…`, `TokenKeyRef::BiscuitIssuer`) = the **cross-vat** carrier: public-key
  (Ed25519) verifiable offline by *anyone* (UCAN-class, attenuation-down-a-chain = keys-as-caps as
  a provenance log). This is what an `Obs` badge wears when it leaves the vat.
- **macaroon** (`em2_…`, `TokenKeyRef::CellScopedMacaroon`) = the **intra-vat** carrier: cell-scoped
  HMAC from a derived root secret — a near-reference convenience *inside* one trust-root, never
  cross-domain (`discoveries.md §6.3`: HMAC ≠ third-party-verifiable).

**Under this candidate's center (the vat-coalgebra), the token is how a vat EXPORTS a cell's c-list
authority across the boundary.** Inside, authority is caps-as-caps — positional CSpace slots the
kernel mediates. On exit, `ρ_out` serializes the held slot into a biscuit key-as-cap; on entry
`ρ_in` re-mints. Both are **lossy, attenuation-only** — the caps→keys forgetful functor Φ (§2.1)
that drops Property F (confinement) + E (revocable forwarders); a key may only narrow.

**Discharge = the await engine's authority-face, and here it is a ▶-guarded *suspended cross-vat
authorization*.** A 3rd-party caveat `cav@Loc⟨cId,vId⟩` is a turn that cannot become admissible
until *another vat* resolves it: the **discharge gateway** = the named resolver, the **discharge
token** (`discharges: Vec<Vec<u8>>`) = the resolution, `bindForRequest = H(M'.sig :: M.sig)` = the
binding-site. This is exactly the coalgebra's `Await` face (§3) over the `AdmissibleTurn` guard —
the cell's unfold blocks on a remote vat's `Obs` advancing past the discharging receipt.

**Revocation is the one consensus seam** (§7): a **negative discharge** — a STARK *non-membership*
proof against an attested revocation root — the de-facto dual of the path-proof. It is the only
op needing globalism, and only **root-epoch agreement**; everything else stays local + offline.
