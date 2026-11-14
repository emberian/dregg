/-
# Dregg2.Distributed.AckBeforeAdmit — the acknowledge-before-admit buffer rule
# (Blocklace paper §5.1–§5.3), authored HERE and exported to the node's ingest path.

**THIS IS LEAN-AUTHORED CONSENSUS LOGIC. Rust calls the exported artifact and decides nothing.**

## The defect this closes

`docs/reference/READING-BLOCKLACE-2026-08-08.md` §0.4 (`e549b1117`): the blocklace's headline
guarantee — *"a Byzantine node may harm only a finite prefix of the computation"* — is
**Proposition 5.5 (Finite Harm)** of the blocklace's own paper (Almeida & Shapiro,
arXiv:2402.08068, `pdfs/blocklace-byzantine-repelling-crdt-almeida-shapiro-2402.08068.pdf`),
and its entire content is the §5.3 **acknowledge-before-admit buffer discipline**. Our buffer
(`node/src/catchup.rs::OrphanBuffer`) buffered on **missing predecessors only**. Without the
acknowledgment condition there is no `R_q(B)` and no bound: BC §5.1 — *"a colluder `p` can remain
undetected indefinitely, allowing it to create any number of blocks, preceded by any number of
blocks from the Byzantine node `q`, indefinitely, and thus polluting the blocklace of any node
accepting `p`-blocks."* The paper proves the colluder can **never** be exposed in finite time
(Def. 5.2: exposure "only at infinity"), so the buffer is not an optimisation over detection —
it is the only thing bounding the damage.

## The rule (BC §5.3, with one deviation, named below)

A received block is staged until its predecessors are present (the existing orphan buffer —
CM Def. 19 *closed*, **unchanged and not relaxed**: it is the hypothesis under DAG-Rider's
same-causal-history property and this repo's `ClosedExtension` discharges). Once closed, a
candidate **head** `h` licenses the batch `S = ⌊h⌋ ∩ D` (its own closure intersected with the
buffer), admitted at once into `B' = B ∪ S`, iff either

1. **first evidence** (BC Def. 5.3 clause 1, §5.1 principle 2): admitting `h` strictly grows
   `byz` — `h` completes a fork (or otherwise first-proves a creator Byzantine). First evidence
   is always admissible; anything else would break eventual visibility of the proof itself.
2. **acknowledged head** (BC Def. 5.3 clause 2 + the `R_q` condition of Prop. 5.5's proof):
   `node(h) ∉ byz(B ∪ S)`, and for EVERY `q ∈ byz(B)` the head's own closure carries the
   evidence (`q ∈ byz(⌊h⌋)` — an incomparable `q`-pair inside `⌊h⌋`), and — the `R_q` tooth —
   if the batch carries any `q`-block then this is the head creator's FIRST acknowledging block
   (`r ∈ R_q(B)`: no prior `r`-block in `B` acknowledges `q`).

## The deviation from Def. 5.3's letter, and why it is the paper's own intent

BC Def. 5.3 read strictly requires a full peeling of `B'` down to `∅` in which EVERY block
satisfies clause 1 or 2 against its growing prefix. That reading refuses every pre-knowledge
block forever: an `r`-block created before `r` saw the evidence has `byz(B) ⊄ byz(⌊b'⌋)` at
every position of every peel (the evidence is already in `B`, hence in every prefix), so it can
never enter — contradicting the paper's own §5.3 narrative (*"except perhaps for some `r`-block
`b'` that precedes some block `b` … with `b'` created before `s` knew `q` to be Byzantine"*),
the proof of Prop. 5.4 (old honest blocks must eventually enter), and §5.1 principle 1.
What Prop. 5.5's proof actually counts is **head-licensed batches**: *"`p` will add a new
`q`-block `b` to `B` only if `b` precedes an `r`-block `b'` for some `r` ∈ R_q(B) such that
`q ∈ byz(b')`"* — the license lives at the head, interior blocks ride in its closure, and the
head's creator must be in `R_q(B)` (no prior acknowledgment). This module implements THAT gate:
clauses checked at the head, batch confined to the head's signed closure, plus the explicit
`R_q`-freshness condition. Without the freshness tooth, bare clause 2 admits an unbounded
laundering replay: a never-equivocating Byzantine `r` that acknowledges the fork in every block
while pointing at fresh `q`-blocks would ferry them in forever. With it, each `(r, q)` pair
licenses q-carriage ONCE — `admit_shrinks_Rq` below — which is exactly the decreasing measure
of the paper's proof.

## What `byz` is here, honestly (the narrowing)

BC §5.2 extends `byz` to `eqvc(B) ∪ {creators of ¬wf / ¬valid / ¬brep blocks}`. This module's
`byzOf` is **`eqvc` only** — equivocators by TRUE incomparability (Def. 4.2, the same shape as
`Authority.Blocklace.Equivocation` / `finality.rs::detect_equivocation`; deliberately NOT the
round-equality subset `hasEquivInPast` tests). Consequences, stated rather than hidden:

* **The harm bound below binds equivocators** (and their colluders). A Byzantine node whose
  misbehavior never includes an equivocation is invisible to this `byz` and is NOT bounded by
  this gate. Forged signatures / unenrolled creators are refused outright by the Rust pin
  (`receive_block_pinned` — BC §4.1 option 1, correct for unverifiable authorship: an unsigned
  block proves nothing about its claimed creator). Non-cordial blocks (CM Def. 25) are the
  named unwired debt of `BlocklaceFinality.isCordialBlock`; the right composition when it is
  wired is BC §4.1 **option 2** — a `¬wf` arm INSIDE `byzOf` (admit the block as evidence,
  flag its creator) — never a discard, which would violate eventual visibility of the evidence,
  and never a hold. The `¬brep(≺b)` recursive arm is likewise future work; with the `R_q`
  freshness tooth above it is not needed for the equivocator bound.

## The harm bound this buys (stated against Prop. 5.5)

Once `B` holds evidence for `q` (`q ∈ byzOf B`), a new `q`-block enters only inside a batch
whose head is first evidence (each such head strictly grows `byzOf` — at most once per creator,
`first_evidence_grows`) or an acknowledging head whose creator is FRESH for `q`
(`admit_shrinks_Rq`: the admission removes that creator from `R_q` — at most once per roster
member). Each batch is `⌊head⌋ ∩ D`, bounded by the Rust buffer cap (`MAX_ORPHANS`). So the
`q`-blocks admitted after evidence number at most
`(|R_q(B)| + |roster \ byz|) × MAX_ORPHANS` — **finite, and q-admission STOPS once `R_q`
drains to colluders**, who by Def. 5.2 never produce an acknowledging head. This is Prop. 5.5's
"finite prefix" — finite but a-priori-unbounded in the paper, here additionally per-batch-capped
— under the paper's own hypotheses (Node Liveness Def. 5.1, connected correct nodes) and the
`byz = eqvc` narrowing above. The count is assembled from the per-step theorems below; the
induction over ingest RUNS (a trace semantics for the buffer loop) is prose, not yet a theorem —
the same class of named boundary as `TauOrderCausal` (stated, `#guard`ed, not proved) in
`BlocklaceFinality`.

## Composition with the other admission-adjacent rules (three rules, one order, no fight)

1. **Closure** (orphan buffer / `MissingPredecessor`) — untouched, evaluated FIRST, and
   re-checked here (`batchClosed`): admission never relaxes it.
2. **Signature/roster pin** (`receive_block_pinned`) — Rust, §8 crypto seam; runs per block ON
   admission, after this gate says yes. A pin refusal drops the block; its dependents re-orphan.
   The gate's `byz(B)` premise therefore only ever reads VERIFIED blocks; batch-interior
   (not-yet-pinned) blocks can never spoof evidence into another head's closure because `S` is
   confined to the head's own signed pointer closure.
3. **THIS GATE** (BC §5.3) — decides WHETHER/WHEN a closed, pinnable block enters the lace.
4. **Exclusion-by-past** (`ExclusionByPast` / τ's anchor-relative `hasEquivInPast`) — decides
   what already-admitted structure COUNTS at ordering time; per-closure, never buffers, never
   refuses ingest. This gate bounds how much excluded material can pile up; exclusion-by-past
   discounts whatever still enters. They compose freely because they act at different times on
   different questions.
5. **Cordiality** (`isCordialBlock`) — defined, still unwired (its own module says so); the
   prescribed composition is the `¬wf` arm of `byzOf` above, NOT a fourth buffer.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}) for the spec theorems;
concrete-trace instances are `native_decide` + `#assert_compiled` (they execute the fuel-bounded
BFS `causalPastIncl`, which does not kernel-reduce under `decide` — the boundary
`BlocklaceFinality` §9 records). Verified with `lake build Dregg2.Distributed.AckBeforeAdmit`.
-/
import Dregg2.Distributed.BlocklaceFinality
import Dregg2.Distributed.FinalityGate

namespace Dregg2.Distributed.AckBeforeAdmit

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.BlocklaceFinality (causalPastIncl closureLace)
open Dregg2.Distributed.FinalityGate
  (parseNat? parseLace? stripReq? decodeLaceWire encodeLaceWire encodeBlockWire)

/-! ## 1. `eqvc` by TRUE incomparability, executably (BC Def. 4.2).

NOT the round-equality subset (`hasEquivInPast`): two same-creator blocks are an equivocation
iff neither observes the other, whatever their rounds. `causalPastIncl B x` is `x`'s INCLUSIVE
causal past, so for distinct ids `a ≺ b ↔ a ∈ ⌊b⌋`. -/

/-- `a ∥ b` — distinct ids, neither in the other's inclusive causal past (BC Def. 4.2's `∥`). -/
def incomparableB (B : Lace) (a b : Block) : Bool :=
  a.id != b.id
    && !(causalPastIncl B b.id).contains a.id
    && !(causalPastIncl B a.id).contains b.id

/-- `q ∈ eqvc(B)`: some incomparable same-creator pair by `q` exists in `B` (the pair need not
be observed by anyone — BC §4.2's remark; `finality.rs::detect_equivocation`). -/
def equivocatesIn (B : Lace) (q : AuthorId) : Bool :=
  B.any fun a => a.creator == q && B.any fun b => b.creator == q && incomparableB B a b

/-- **`byzOf B`** — `byz(B)` under the `eqvc`-only narrowing (module docblock): the distinct
creators of `B` that equivocate in `B`. -/
def byzOf (B : Lace) : List AuthorId :=
  ((B.map (·.creator)).dedup).filter (equivocatesIn B)

/-- **`acksByz B b q`** — `q ∈ byz(⌊b⌋)`: an incomparable `q`-pair inside `b`'s OWN closure.
This is the block-level acknowledgment BC §5.3 waits for, and the executable twin of
`ExclusionByPast.ByzInClosure` (which proves the agreement/durability/partial-view poles of
exactly this per-closure shape at the `Prop` level). `acksByz B b b.creator` is the executable
`ExcludedByPast`. -/
def acksByz (B : Lace) (b : Block) (q : AuthorId) : Bool :=
  equivocatesIn (closureLace B b.id) q

/-- `r` already has an acknowledging block for `q` in `B` — the negation of `r ∈ R_q(B)`'s
second condition (Prop. 5.5's proof). -/
def hadAcked (B : Lace) (r q : AuthorId) : Bool :=
  B.any fun b => b.creator == r && acksByz B b q

/-- The batch carries a `q`-block. -/
def carriesBlockBy (S : Lace) (q : AuthorId) : Bool :=
  S.any fun s => s.creator == q

/-- **`Rq B roster q`** — the paper's `R_q(B)` (proof of Prop. 5.5): roster members not
themselves flagged and with no acknowledging block for `q` in `B`. The decreasing measure of
the finite-harm argument. -/
def Rq (B : Lace) (roster : List AuthorId) (q : AuthorId) : List AuthorId :=
  roster.filter fun r => !(byzOf B).contains r && !hadAcked B r q

/-! ## 2. The batch and the gate (BC §5.3: `S = ⌊b⌋ ∩ D`, admitted at once). -/

/-- `U` with the head removed — the `B \ {b}` of Def. 5.3 clause 1. -/
def sans (U : Lace) (h : BlockId) : Lace := U.filter (fun b => b.id != h)

/-- **`batchOf B D h`** — `S = ⌊h⌋ ∩ D`: the buffered blocks inside the head's own closure,
computed over `B ∪ D`. Confinement to the head's SIGNED closure is load-bearing: nothing an
adversary places in `D` can enter (or influence the head-clean check through) a batch whose
head does not point at it. -/
def batchOf (B D : Lace) (h : BlockId) : Lace :=
  let past := causalPastIncl (B ++ D) h
  D.filter fun d => past.contains d.id

/-- **`batchClosed B S`** — every predecessor of every batch member resolves in `B ∪ S`
(BC §5.3's `⌊S⌋ ⊆ B ∪ S`; CM Def. 19 *closed*). The closure gate, RE-CHECKED at admission —
never relaxed. -/
def batchClosed (B S : Lace) : Bool :=
  S.all fun s => s.preds.all fun p => (B ++ S).has p

/-- **Clause 1 — first evidence** (Def. 5.3.1, principle 2): removing the head shrinks `byz`,
i.e. the head is essential to some creator's flagging. -/
def firstEvidence (B S : Lace) (h : BlockId) : Bool :=
  (byzOf (B ++ S)).any fun q => !(byzOf (sans (B ++ S) h)).contains q

/-- **Clause 2 — acknowledged head** (Def. 5.3.2 + the `R_q` condition): head's creator is not
Byzantine in `B ∪ S`; the head's own closure acknowledges EVERY currently-known Byzantine; and
for each `q` the batch carries blocks of, this is the creator's FIRST acknowledgment
(`replay_refused` is the tooth this last conjunct grows). -/
def headLicensed (B S : Lace) (hb : Block) : Bool :=
  !(byzOf (B ++ S)).contains hb.creator
    && (byzOf B).all fun q =>
         acksByz (B ++ S) hb q
           && (!carriesBlockBy S q || !hadAcked B hb.creator q)

/-- **THE GATE** — BC §5.3's admission procedure for head candidate `h` against lace `B` and
buffer `D`: the head must be a buffered block, the batch closed, and clause 1 or clause 2 hold.
The Rust ingest (`node/src/catchup.rs::apply_with_buffering`) consults this (via the export
below) before ANY insert once a fork is known, and holds the block otherwise. -/
def admitBatch (B D : Lace) (h : BlockId) : Bool :=
  match (batchOf B D h).lookup h with
  | none => false
  | some hb =>
      batchClosed B (batchOf B D h)
        && (firstEvidence B (batchOf B D h) h || headLicensed B (batchOf B D h) hb)

/-- The admitted batch in an insertion order compatible with `≺` (closure sizes ascending:
`a ≺ b ⇒ ⌊a⌋ ⊊ ⌊b⌋ ⇒ |⌊a⌋| < |⌊b⌋|`). The Rust side re-verifies each emitted block through
`receive_block_pinned`, which enforces closure per insert — a mis-ordered emission cannot
corrupt the lace, only re-orphan. -/
def batchOrder (B D : Lace) (h : BlockId) : List BlockId :=
  let S := batchOf B D h
  let U := B ++ S
  ((S.map fun s => (s.id, (causalPastIncl U s.id).length)).mergeSort
      (fun a b => a.2 ≤ b.2)).map (·.1)

/-! ## 3. Spec theorems — the gate's promises, named. -/

/-- The gate's whole truth condition, given the head resolves in its batch. Everything below is
a corollary, named separately because each is a distinct promise the ingest relies on. -/
theorem admit_iff {B D : Lace} {h : BlockId} {hb : Block}
    (hS : (batchOf B D h).lookup h = some hb) :
    admitBatch B D h = true ↔
      (batchClosed B (batchOf B D h) = true
        ∧ (firstEvidence B (batchOf B D h) h = true
            ∨ headLicensed B (batchOf B D h) hb = true)) := by
  unfold admitBatch
  rw [hS]
  simp [Bool.and_eq_true, Bool.or_eq_true]

/-- **Admission requires closure** — the gate can only ever STRENGTHEN the predecessor check,
never weaken it ("do not relax the closure gate", as a theorem). -/
theorem admit_requires_closed {B D : Lace} {h : BlockId}
    (h1 : admitBatch B D h = true) : batchClosed B (batchOf B D h) = true := by
  unfold admitBatch at h1
  rcases hl : (batchOf B D h).lookup h with _ | hb
  · rw [hl] at h1; exact absurd h1 (by simp)
  · rw [hl] at h1; exact ((Bool.and_eq_true _ _).mp h1).1

/-- **Admission is licensed** — every admission is first evidence or an acknowledged head.
The contrapositive is the colluder pole: no license, no entry, forever. -/
theorem admit_is_licensed {B D : Lace} {h : BlockId} {hb : Block}
    (hS : (batchOf B D h).lookup h = some hb)
    (h1 : admitBatch B D h = true) :
    firstEvidence B (batchOf B D h) h = true
      ∨ headLicensed B (batchOf B D h) hb = true :=
  ((admit_iff hS).mp h1).2

/-- A licensed head acknowledges EVERY currently-known Byzantine, and carries `q`-blocks only
as its creator's first acknowledgment of `q`. -/
theorem licensed_head_acks {B S : Lace} {hb : Block} {q : AuthorId}
    (hlic : headLicensed B S hb = true) (hq : q ∈ byzOf B) :
    acksByz (B ++ S) hb q = true
      ∧ (carriesBlockBy S q = true → hadAcked B hb.creator q = false) := by
  unfold headLicensed at hlic
  have hall := ((Bool.and_eq_true _ _).mp hlic).2
  have hqq := (List.all_eq_true.mp hall) q hq
  have h1 := ((Bool.and_eq_true _ _).mp hqq).1
  have h2 := ((Bool.and_eq_true _ _).mp hqq).2
  refine ⟨h1, fun hc => ?_⟩
  rcases (Bool.or_eq_true _ _).mp h2 with hnc | hnh
  · rw [hc] at hnc; exact absurd hnc (by simp)
  · simpa using hnh

/-- **The colluder pole** — a head that does not acknowledge a known Byzantine is never
licensed. A colluder (Def. 5.2: NO block ever acknowledges `q`) therefore never licenses a
batch; its stream is held forever, and with it every `q`-block it ferries. -/
theorem unacknowledging_head_refused {B S : Lace} {hb : Block} {q : AuthorId}
    (hq : q ∈ byzOf B) (hnoack : acksByz (B ++ S) hb q = false) :
    headLicensed B S hb = false := by
  cases hcase : headLicensed B S hb
  · rfl
  · exact absurd (licensed_head_acks hcase hq).1 (by simp [hnoack])

/-- **A known equivocator's own block never licenses** (clause 2's creator-clean conjunct). -/
theorem byz_creator_head_refused {B S : Lace} {hb : Block}
    (h : (byzOf (B ++ S)).contains hb.creator = true) :
    headLicensed B S hb = false := by
  unfold headLicensed
  rw [h]
  rfl

/-- **The laundering replay is refused** — once the head's creator has acknowledged `q`, no
later head by the same creator may carry `q`-blocks. Bare clause 2 admits this replay without
bound; this is the `r ∈ R_q(B)` condition of Prop. 5.5's proof, as a refusal theorem. -/
theorem replay_refused {B S : Lace} {hb : Block} {q : AuthorId}
    (hq : q ∈ byzOf B) (hcarry : carriesBlockBy S q = true)
    (hprior : hadAcked B hb.creator q = true) :
    headLicensed B S hb = false := by
  cases hcase : headLicensed B S hb
  · rfl
  · have := (licensed_head_acks hcase hq).2 hcarry
    rw [hprior] at this
    exact absurd this (by simp)

/-- **The measure decreases** (Prop. 5.5's proof step): an acknowledged-head admission removes
the head's creator from `R_q` of the POST-admission lace — the head itself is now the
acknowledging block. Each `(creator, q)` pair can therefore drain from `R_q` at most once, and
`R_q` never refills (acknowledgments are blocks; blocks are never removed). -/
theorem admit_shrinks_Rq {B D : Lace} {h : BlockId} {hb : Block} {q : AuthorId}
    {roster : List AuthorId}
    (hS : (batchOf B D h).lookup h = some hb)
    (hlic : headLicensed B (batchOf B D h) hb = true)
    (hq : q ∈ byzOf B) :
    hb.creator ∉ Rq (B ++ batchOf B D h) roster q := by
  intro hmem
  have hfilter := (List.mem_filter.mp hmem).2
  have hnoack : hadAcked (B ++ batchOf B D h) hb.creator q = false := by
    have h2 := ((Bool.and_eq_true _ _).mp hfilter).2
    simpa using h2
  -- but the head IS an acknowledging block of its own creator in B ++ S:
  have hbmem : hb ∈ B ++ batchOf B D h :=
    List.mem_append_right _ (List.mem_of_find?_eq_some hS)
  have hacks : acksByz (B ++ batchOf B D h) hb q = true :=
    (licensed_head_acks hlic hq).1
  have : hadAcked (B ++ batchOf B D h) hb.creator q = true :=
    List.any_eq_true.mpr ⟨hb, hbmem, by simp [hacks]⟩
  rw [hnoack] at this
  exact absurd this (by simp)

/-- **First evidence grows `byz`** — each clause-1 admission flags a creator not flagged
without the head. Since `byzOf ⊆` the lace's creators and the deployed roster is finite and
pinned (`receive_block_pinned` refuses unenrolled creators), clause-1 admissions after evidence
for `q` exists are bounded by the roster size. -/
theorem first_evidence_grows {B S : Lace} {h : BlockId}
    (hfe : firstEvidence B S h = true) :
    ∃ q, q ∈ byzOf (B ++ S) ∧ (byzOf (sans (B ++ S) h)).contains q = false := by
  obtain ⟨q, hqmem, hqfresh⟩ := List.any_eq_true.mp hfe
  exact ⟨q, hqmem, by simpa using hqfresh⟩

/-- **The liveness pole's license** — with NO known Byzantine anywhere in sight (empty
`byzOf B`) and a clean head, a closed batch is ALWAYS admitted: the buffer never delays an
honest stream in a fork-free lace. This theorem is what licenses the Rust fast path
(`catchup.rs` skips the FFI entirely when `lace.equivocators()` is empty and nothing is held —
the gate would answer yes by this theorem, together with `first_evidence` covering the arrival
that completes a fork). -/
theorem no_byz_no_hold {B D : Lace} {h : BlockId} {hb : Block}
    (hS : (batchOf B D h).lookup h = some hb)
    (hcl : batchClosed B (batchOf B D h) = true)
    (hnobyz : byzOf B = [])
    (hclean : (byzOf (B ++ batchOf B D h)).contains hb.creator = false) :
    admitBatch B D h = true := by
  rw [admit_iff hS]
  refine ⟨hcl, Or.inr ?_⟩
  unfold headLicensed
  rw [hclean, hnobyz]
  rfl

/-- **The acknowledging head admits** — the batch-carry case (BC §5.3's narrative: a lagging
honest peer's backlog rides in under its first acknowledging block). Together with
`unacknowledging_head_refused` these are the two poles: held while silent on the fork, admitted
the moment its own chain acknowledges it. -/
theorem acknowledging_head_admits {B D : Lace} {h : BlockId} {hb : Block}
    (hS : (batchOf B D h).lookup h = some hb)
    (hcl : batchClosed B (batchOf B D h) = true)
    (hclean : (byzOf (B ++ batchOf B D h)).contains hb.creator = false)
    (hacks : ∀ q ∈ byzOf B,
      acksByz (B ++ batchOf B D h) hb q = true
        ∧ (carriesBlockBy (batchOf B D h) q = true → hadAcked B hb.creator q = false)) :
    admitBatch B D h = true := by
  rw [admit_iff hS]
  refine ⟨hcl, Or.inr ?_⟩
  unfold headLicensed
  rw [hclean]
  refine (Bool.and_eq_true _ _).mpr ⟨rfl, ?_⟩
  refine List.all_eq_true.mpr fun q hq => ?_
  obtain ⟨h1, h2⟩ := hacks q hq
  refine (Bool.and_eq_true _ _).mpr ⟨h1, ?_⟩
  cases hc : carriesBlockBy (batchOf B D h) q
  · rfl
  · rw [h2 hc]; rfl

#assert_axioms admit_iff
#assert_axioms admit_requires_closed
#assert_axioms admit_is_licensed
#assert_axioms licensed_head_acks
#assert_axioms unacknowledging_head_refused
#assert_axioms byz_creator_head_refused
#assert_axioms replay_refused
#assert_axioms admit_shrinks_Rq
#assert_axioms first_evidence_grows
#assert_axioms no_byz_no_hold
#assert_axioms acknowledging_head_admits

/-! ## 4. Concrete traces — BOTH POLES witnessed, mutation asserted present BEFORE each verdict.

The welded fork lace: honest 7 authors genesis `bG` and the CARRIER `bW` pointing at BOTH
halves of equivocator 9's fork (`bF1 ∥ bF2`) — exactly the shape the Rust two-tips evidence
floor (`CreatorTips::Pair`, `89238335a`) produces on detection. -/

def bG  : Block := ⟨0, 7, 0, [], true⟩
def bF1 : Block := ⟨2, 9, 1, [0], true⟩
def bF2 : Block := ⟨3, 9, 1, [0], true⟩
def bW  : Block := ⟨4, 7, 1, [2, 3], true⟩
def laceFork : Lace := [bG, bF1, bF2, bW]

/-- ⚑ MUTATION ASSERTED PRESENT: the fork is real and detected — author 9, and only author 9,
is Byzantine in the base lace of every witness below. -/
theorem byz_laceFork : byzOf laceFork = [9] := by native_decide

-- ── PRE-STORY: first evidence and the carrier are themselves admissible (principle 2).
/-- The second fork half is first evidence: admitted alone, no acknowledgment required. -/
theorem second_half_admits_as_first_evidence :
    admitBatch [bG, bF1] [bF2] 3 = true := by native_decide
/-- The evidence carrier (pointing at both halves) is an acknowledged head. -/
theorem carrier_admits : admitBatch [bG, bF1, bF2] [bW] 4 = true := by native_decide

-- ── POLE A (liveness): a lagging honest peer (author 5) authored `bD1, bD2` before seeing the
-- fork. Its stream is HELD while silent on the fork, and the whole backlog is admitted at once
-- under its first acknowledging block `bD3` (which points at the carrier).
def bD1 : Block := ⟨10, 5, 0, [0], true⟩
def bD2 : Block := ⟨11, 5, 1, [10], true⟩
def bD3 : Block := ⟨12, 5, 2, [11, 4], true⟩

theorem lagging_honest_held :
    admitBatch laceFork [bD1, bD2] 10 = false
      ∧ admitBatch laceFork [bD1, bD2] 11 = false := by native_decide

theorem lagging_honest_backlog_admitted_under_acking_head :
    admitBatch laceFork [bD1, bD2, bD3] 12 = true
      ∧ batchOrder laceFork [bD1, bD2, bD3] 12 = [10, 11, 12] := by native_decide

-- ── POLE B (the bound): a colluder (author 6) feeds equivocator 9's continued stream
-- (`bE3, bE4`) topped by its own never-acknowledging block `bC1`. EVERY head candidate is
-- refused: zero blocks enter, and will never enter while no head acknowledges.
def bE3 : Block := ⟨20, 9, 2, [2], true⟩
def bE4 : Block := ⟨21, 9, 3, [20], true⟩
def bC1 : Block := ⟨22, 6, 0, [21], true⟩

/-- ⚑ MUTATION ASSERTED PRESENT: the fed stream really carries `q = 9` blocks, and the
colluder head really does NOT acknowledge 9 (its closure holds only one branch). -/
theorem colluder_stream_mutation_present :
    carriesBlockBy [bE3, bE4, bC1] 9 = true
      ∧ acksByz (laceFork ++ [bE3, bE4, bC1]) bC1 9 = false := by native_decide

theorem colluder_fed_stream_fully_held :
    admitBatch laceFork [bE3, bE4, bC1] 20 = false
      ∧ admitBatch laceFork [bE3, bE4, bC1] 21 = false
      ∧ admitBatch laceFork [bE3, bE4, bC1] 22 = false := by native_decide

-- ── POLE B′ (the R_q tooth): a never-equivocating Byzantine relay (author 8) that DOES
-- acknowledge the fork can ferry `q`-blocks in ONCE (its first acknowledgment — the paper's
-- legitimate pre-knowledge backlog, and the R_q drain step). The REPLAY is refused; a q-free
-- later head still admits (the relay's ordinary participation is unimpeded).
def bL1 : Block := ⟨30, 8, 0, [4, 20], true⟩
def lace2 : Lace := laceFork ++ [bE3, bL1]
def bE5 : Block := ⟨31, 9, 3, [20], true⟩
def bL2 : Block := ⟨32, 8, 1, [30, 31], true⟩
def bL3 : Block := ⟨33, 8, 1, [30], true⟩

theorem first_ack_ferries_once : admitBatch laceFork [bE3, bL1] 30 = true := by native_decide

/-- ⚑ MUTATION ASSERTED PRESENT: after `bL1` lands, author 8 HAS acknowledged 9, and the
replay batch really carries a fresh 9-block. -/
theorem replay_mutation_present :
    hadAcked lace2 8 9 = true ∧ carriesBlockBy [bE5, bL2] 9 = true := by native_decide

theorem laundering_replay_refused : admitBatch lace2 [bE5, bL2] 32 = false := by native_decide
theorem q_free_head_still_admits : admitBatch lace2 [bL3] 33 = true := by native_decide

-- ── The measure, concretely: admitting 8's acknowledging head drains 8 from R₉. (7 is already
-- out — the carrier `bW` is its acknowledgment; 5 and 6 remain until they acknowledge.)
theorem Rq_drains_concretely :
    Rq laceFork [5, 6, 7, 8] 9 = [5, 6, 8]
      ∧ Rq lace2 [5, 6, 7, 8] 9 = [5, 6] := by native_decide

#assert_compiled byz_laceFork
#assert_compiled second_half_admits_as_first_evidence
#assert_compiled carrier_admits
#assert_compiled lagging_honest_held
#assert_compiled lagging_honest_backlog_admitted_under_acking_head
#assert_compiled colluder_stream_mutation_present
#assert_compiled colluder_fed_stream_fully_held
#assert_compiled first_ack_ferries_once
#assert_compiled replay_mutation_present
#assert_compiled laundering_replay_refused
#assert_compiled q_free_head_still_admits
#assert_compiled Rq_drains_concretely

/-! ## 5. THE WIRE — `@[export] dregg_ack_admit`, the `FinalityGate`/`RoundAdvanceGate`
template. The lace segment reuses `FinalityGate`'s grammar; this gate prefixes the head id and
the buffered set.

```
INPUT  := "h=" Nat ";D=" (BLOCKW ("|" BLOCKW)*)? ";" LACEWIRE
LACEWIRE := "w=" Nat ";P=" ... ";B=" ...            -- FinalityGate's (wavelength, P, lace);
                                                    --   w and P are carried, not consulted
OUTPUT := "1:" (Nat ("," Nat)*)?                    -- admit: batch ids, insertion order
        | "0"                                       -- hold (fail-closed on refusal)
        | "ERR"                                     -- parse failure (fail-closed sentinel:
                                                    --   the node HOLDS — a parse failure
                                                    --   never admits)
```
-/

/-- Decode the ack-admit wire. Fail-closed on any deviation. -/
def decodeAckWire (s : String) : Option (BlockId × Lace × Nat × List AuthorId × Lace) := do
  let rest ← stripReq? "h=" s
  match rest.splitOn ";" with
  | hS :: dSeg :: tail =>
      let h ← parseNat? hS
      let dS ← stripReq? "D=" dSeg
      let D ← parseLace? dS
      let (w, parts, B) ← decodeLaceWire (String.intercalate ";" tail)
      some (h, D, w, parts, B)
  | _ => none

/-- Encode an ack-admit query (the inverse the node's Rust encoder mirrors). -/
def encodeAckWire (h : BlockId) (D : Lace) (w : Nat) (parts : List AuthorId) (B : Lace) :
    String :=
  "h=" ++ toString h ++ ";D=" ++ String.intercalate "|" (D.map encodeBlockWire) ++ ";"
    ++ encodeLaceWire w parts B

/-- **The gate body**: decode ⤳ `admitBatch` ⤳ `"1:<batch>"`/`"0"`, `"ERR"` fail-closed. -/
def ackWireGate (s : String) : String :=
  match decodeAckWire s with
  | some (h, D, _w, _parts, B) =>
      if admitBatch B D h then
        "1:" ++ String.intercalate "," ((batchOrder B D h).map toString)
      else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_ack_admit]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi/src/distributed_ffi.rs::shadow_ack_admit`) calls from
`node/src/catchup.rs::apply_with_buffering` once a fork is known. -/
@[export dregg_ack_admit]
def dregg_ack_admit (s : String) : String := ackWireGate s

/-- **The export carries the proof** (the `round_advance_eq_gate` shape): for any wire that
decodes, the exported verdict IS the verified `admitBatch` — the node consulting the export is
consulting the rule every theorem above is about, by construction. -/
theorem ack_admit_eq_gate (s : String) (h : BlockId) (D : Lace) (w : Nat)
    (parts : List AuthorId) (B : Lace)
    (hdec : decodeAckWire s = some (h, D, w, parts, B)) :
    dregg_ack_admit s
      = (if admitBatch B D h then
          "1:" ++ String.intercalate "," ((batchOrder B D h).map toString)
        else "0") := by
  unfold dregg_ack_admit ackWireGate
  rw [hdec]

#assert_axioms ack_admit_eq_gate

-- ── wire-level witnesses: round-trip, both verdicts, and the fail-closed sentinel.
theorem wire_roundtrip :
    decodeAckWire (encodeAckWire 12 [bD1, bD2, bD3] 0 [] laceFork)
      = some (12, [bD1, bD2, bD3], 0, [], laceFork) := by native_decide
theorem wire_admits_backlog :
    ackWireGate (encodeAckWire 12 [bD1, bD2, bD3] 0 [] laceFork) = "1:10,11,12" := by
  native_decide
theorem wire_holds_colluder :
    ackWireGate (encodeAckWire 22 [bE3, bE4, bC1] 0 [] laceFork) = "0" := by native_decide
theorem wire_malformed_errs : ackWireGate "not a wire" = "ERR" := by native_decide

#assert_compiled wire_roundtrip
#assert_compiled wire_admits_backlog
#assert_compiled wire_holds_colluder
#assert_compiled wire_malformed_errs

end Dregg2.Distributed.AckBeforeAdmit
