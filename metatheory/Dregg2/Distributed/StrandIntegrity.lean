/-
# Dregg2.Distributed.StrandIntegrity — the per-creator FEED projection of the lace,
# and the feed-integrity (C1) the FIXED `blocklace/src/lib.rs::insert` enforces.

**The gap this closes (audit A1 / property C1, `.docs-history-noclaude/rebuild/metatheory/_FEDERATION-SSB-DESIGN.md`).**
A **strand** is a Secure-Scuttlebutt feed: a single creator's append-only, Ed25519-signed,
monotone-sequence log — the SSB notion dregg inherits (`blocklace/src/lib.rs:80-94`, the
`creator`/`sequence`/`predecessors`/`signature` fields). The lace's `tips[creator]` /
`tip_sequence[creator]` (`lib.rs:339-342`) IS that feed's head.

The OLD `insert` (`lib.rs:189-225` in the audit) checked only causal closure: it did NOT verify
the Ed25519 signature, did NOT enforce per-creator `sequence` monotonicity, and **silently
overwrote** `tips[creator]`, so two blocks at the same `(creator, seq)` were both stored as live
state — an undetected fork. The FIXED `insert` (this branch, `lib.rs::insert`):
(1) verifies the signature, (2) enforces `sequence` strictly exceeds the creator's tip, and
(3) on a second distinct block at an existing `(creator, seq)` RETAINS it as a detectable
`EquivocationProof` and **withdraws the tip** rather than overwriting it.

**What is NEW here vs `Dregg2/Authority/Blocklace.lean`.** That module already models `Block`,
`Lace`, `precedes`/`incomparable`, `Equivocation`/`Equivocator`, `equivocation_detectable`, and
`honest_no_equivocation` (the *lace-wide, content-independent* fork theorems). It does NOT model
the **per-creator FEED projection** or the **single-tip / monotone-sequence** invariants that the
*write path* (`insert`) maintains. This file builds exactly that new piece:

* `Strand B p` — the per-creator projection (filter the lace by `creator = p`); the SSB feed.
* `StrandForkFree` — no two *distinct* blocks at one `(creator, seq)`: the no-equivocation-at-a-
  slot invariant the FIXED `insert` keeps (and the OLD overwriting `insert` did not).
* `seq_monotone` / `appendOnly` — the monotone-sequence + grow-only feed shape.
* **`strand_single_tip`** — a fork-free strand has a UNIQUE block at its tip sequence (one feed
  head). The keystone.
* `insertStrandOk` (the verified write path: reject same-seq-distinct) **preserves** fork-freedom;
  `insertOverwrite` (the OLD path) does **not** — a NEG witness exhibiting the dropped fork.
* `forkFree_of_honestChain` — connects to the existing `HonestChain` so the new projection layer
  sits atop the existing lace theory rather than duplicating it.

We import `Authority/Blocklace.lean` and `Distributed/BlocklaceFinality.lean` READ-ONLY and reuse
`Block`/`Lace`/`Equivocation`/`HonestChain`. We do NOT edit `RecordKernel.lean`; the receipt-chain
connection (a cell's own append-only log IS a strand) is stated as a hypothesis-level remark, not
an import.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Pure, computable, `#guard`-checked non-vacuity. Verified with
`lake build Dregg2.Distributed.StrandIntegrity`.
-/
import Dregg2.Authority.Blocklace
import Dregg2.Distributed.BlocklaceFinality

namespace Dregg2.Distributed.StrandIntegrity

open Dregg2.Authority.Blocklace
  (Block Lace BlockId AuthorId Equivocation Equivocator HonestChain)

/-! ## 1. The strand — the per-creator FEED projection of the lace.

`Strand B p` filters the lace `B` to the blocks authored by `p` (`b.creator = p`). This IS the SSB
feed: the author's own log. In the Rust write path this is the chain whose head is `tips[p]` and
whose length tracks `tip_sequence[p]` (`lib.rs:339-342`). The lace is the DAG woven from all
strands; the strand is one creator's slice of it. -/

/-- **`Strand B p`** — the sub-lace of `B` authored by `p` (the SSB feed of `p`). -/
def Strand (B : Lace) (p : AuthorId) : Lace :=
  B.filter (fun b => b.creator = p)

/-- A block is **on** `p`'s strand iff it is in `B` and authored by `p`. -/
theorem mem_strand_iff {B : Lace} {p : AuthorId} {b : Block} :
    b ∈ Strand B p ↔ b ∈ B ∧ b.creator = p := by
  simp [Strand, List.mem_filter]

/-- Every block on `p`'s strand is authored by `p` (`b.creator = p`). -/
theorem strand_creator {B : Lace} {p : AuthorId} {b : Block} (h : b ∈ Strand B p) :
    b.creator = p := (mem_strand_iff.mp h).2

/-- Every block on `p`'s strand is in the lace `B`. -/
theorem strand_subset {B : Lace} {p : AuthorId} {b : Block} (h : b ∈ Strand B p) :
    b ∈ B := (mem_strand_iff.mp h).1

/-- The sequence numbers present on `p`'s strand (the feed positions it occupies). -/
def strandSeqs (B : Lace) (p : AuthorId) : List Nat :=
  (Strand B p).map (·.seq)

/-- **`strandTipSeq`** — the feed head's sequence: the maximum `seq` on the strand (`0` for an
empty strand). This is the Rust `tip_sequence[p]` (`lib.rs:342`), the strand's length-marker. -/
def strandTipSeq (B : Lace) (p : AuthorId) : Nat :=
  (strandSeqs B p).foldr Nat.max 0

/-- Helper: `foldr Nat.max 0` dominates every element of the list. -/
theorem le_foldr_max : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr Nat.max 0
  | [], _, hmem => by simp at hmem
  | y :: t, x, hmem => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact Nat.le_max_left _ _
    · exact le_trans (le_foldr_max t x htl) (Nat.le_max_right _ _)

/-- Helper: on a non-empty list, `foldr Nat.max 0` is attained (it is a member of the list). -/
theorem foldr_max_mem : ∀ (l : List Nat), l ≠ [] → l.foldr Nat.max 0 ∈ l
  | [], hne => absurd rfl hne
  | [x], _ => by simp
  | x :: y :: t, _ => by
    have hfold : (x :: y :: t).foldr Nat.max 0 = Nat.max x ((y :: t).foldr Nat.max 0) := rfl
    rw [hfold]
    have htail := foldr_max_mem (y :: t) (by simp)
    rcases Nat.le_total x ((y :: t).foldr Nat.max 0) with hle | hge
    · have : Nat.max x ((y :: t).foldr Nat.max 0) = (y :: t).foldr Nat.max 0 :=
        Nat.max_eq_right hle
      rw [this]; exact List.mem_cons_of_mem _ htail
    · have : Nat.max x ((y :: t).foldr Nat.max 0) = x := Nat.max_eq_left hge
      rw [this]; exact List.mem_cons_self

/-- The tip sequence dominates every block's `seq` on the strand: no feed position exceeds the
head. (`tip_sequence[p]` is the max, so a new block must *strictly exceed* it to extend —
the `SeqRegression` guard, `lib.rs:428-438`.) -/
theorem le_strandTipSeq {B : Lace} {p : AuthorId} {b : Block}
    (h : b ∈ Strand B p) : b.seq ≤ strandTipSeq B p :=
  le_foldr_max (strandSeqs B p) b.seq (List.mem_map_of_mem h)

/-! ## 2. Fork-freedom — the no-equivocation-at-a-slot write invariant.

The FIXED `insert` rejects a *second, distinct* block at an already-occupied `(creator, seq)`
(`lib.rs::find_conflict` + the `Equivocation` arm, `:402-423`). The resulting invariant on the
strand: **at most one block per sequence number**. This is the strand-layer projection of the
lace-wide `Equivocation` notion — but stated as a *function* (`seq ↦ unique block`), which is what
"a single append-only feed head" needs and what the existing `Blocklace.lean` does not provide. -/

/-- **`StrandForkFree B p`** — `p`'s feed holds at most one block per sequence: any two strand
blocks with equal `seq` are equal. The invariant the FIXED `insert` maintains; the OLD overwriting
`insert` violated it (it stored both forks). -/
def StrandForkFree (B : Lace) (p : AuthorId) : Prop :=
  ∀ a ∈ Strand B p, ∀ b ∈ Strand B p, a.seq = b.seq → a = b

/-- **`StrandSeqMonotone B p`** — distinct strand blocks have distinct sequences (the contrapositive
shape of fork-freedom for the seq field): an injective `seq` over the feed, so the feed is laid out
along the sequence axis with no collisions. -/
def StrandSeqMonotone (B : Lace) (p : AuthorId) : Prop :=
  ∀ a ∈ Strand B p, ∀ b ∈ Strand B p, a ≠ b → a.seq ≠ b.seq

/-- Fork-freedom and seq-monotonicity are the same invariant (contrapositive). -/
theorem forkFree_iff_seqMonotone {B : Lace} {p : AuthorId} :
    StrandForkFree B p ↔ StrandSeqMonotone B p := by
  constructor
  · intro h a ha b hb hne hseq; exact hne (h a ha b hb hseq)
  · intro h a ha b hb hseq; by_contra hne; exact h a ha b hb hne hseq

/-! ## 3. THE KEYSTONE — a fork-free strand has a SINGLE tip (one feed head).

The whole point of the A1 fix: after it, `tips[creator]` is a *function* — there is exactly one
feed head. We prove that on a fork-free, non-empty strand, the block at the tip sequence is
**unique**: any two blocks both sitting at `strandTipSeq` are equal. (The OLD `insert` could leave
two live blocks at the head sequence — no single tip; see §5's NEG witness.) -/

/-- A non-empty strand actually attains its tip sequence: some block sits at `strandTipSeq`. -/
theorem exists_tip_block {B : Lace} {p : AuthorId} (hne : Strand B p ≠ []) :
    ∃ b ∈ Strand B p, b.seq = strandTipSeq B p := by
  -- `strandTipSeq` is the foldr-max of the seq list; on a non-empty list that max is attained.
  have hsne : strandSeqs B p ≠ [] := by
    simpa [strandSeqs] using (List.map_eq_nil_iff (f := (·.seq)) (l := Strand B p)).not.mpr hne
  -- the foldr-max is a member of the seq list, hence the seq of some strand block.
  have hmem : strandTipSeq B p ∈ strandSeqs B p := foldr_max_mem (strandSeqs B p) hsne
  obtain ⟨b, hb, hbseq⟩ := List.mem_map.mp hmem
  exact ⟨b, hb, hbseq⟩

/-- **`strand_single_tip`** — THE single-feed-head guarantee. On a fork-free strand, the tip block
(the block at `strandTipSeq`) is UNIQUE: any two strand blocks both at the tip sequence are equal.
This is what `tips[creator]` being a well-defined single head *means*, and exactly what the FIXED
`insert` enforces by rejecting a second block at an occupied seq (`lib.rs:402-423`). -/
theorem strand_single_tip {B : Lace} {p : AuthorId} (hff : StrandForkFree B p)
    {a b : Block} (ha : a ∈ Strand B p) (hb : b ∈ Strand B p)
    (hatip : a.seq = strandTipSeq B p) (hbtip : b.seq = strandTipSeq B p) :
    a = b :=
  hff a ha b hb (hatip.trans hbtip.symm)

/-- **`tip_block_exists_unique`** — packaging: a fork-free non-empty strand has *exactly one* tip
block (existence from `exists_tip_block`, uniqueness from `strand_single_tip`). The feed head is a
total function of the strand. -/
theorem tip_block_exists_unique {B : Lace} {p : AuthorId}
    (hff : StrandForkFree B p) (hne : Strand B p ≠ []) :
    ∃! b, b ∈ Strand B p ∧ b.seq = strandTipSeq B p := by
  obtain ⟨t, ht, htseq⟩ := exists_tip_block hne
  refine ⟨t, ⟨ht, htseq⟩, ?_⟩
  rintro b ⟨hb, hbseq⟩
  exact strand_single_tip hff hb ht hbseq htseq

/-! ## 4. The bridge to the existing lace theory — honest authors are fork-free.

`Authority/Blocklace.lean::HonestChain` says `p`'s blocks are `≺`-totally-ordered (each acks the
prior tip). We connect: under `HonestChain` *and* the content-addressing `Canonical`, distinct
same-seq blocks cannot both be present — so the strand is fork-free. This makes the new projection
invariant a CONSEQUENCE of the existing honest-discipline model, not a fresh axiom.

The lemma we need from the existing theory: an honest chain has no incomparable pair, hence no two
distinct blocks at one seq that are concurrent. We additionally use that two DISTINCT same-author
same-seq blocks are necessarily incomparable in any acyclic lace where `≺` strictly increases
`seq` — captured here as the hypothesis `seqStrictMono` (the §-free semantic content of "an ack
edge goes to a strictly-earlier feed position"). -/

/-- **`SeqStrictMono B`** — along any `≺` (causal-ack) step the source sits at a strictly smaller
`seq` than the target. This is the honest virtual-chain layout (`add_block` acks the prior tip, so
`seq` strictly increases down the chain). A semantic order fact (no crypto).

⚠ It is a hypothesis about ONE author's chain read across authors, and across authors it is false
on ordinary laces: a validator that joins late writes `seq 0` citing blocks with `seq 2`
(`BlocklaceFinality.traceLateFirst`). `BlocklaceFinality.computeRounds` used to assume exactly
this — it folded in `(seq, creator)` order — and gave that block the wrong round (dregg issue
#100); it no longer relies on `seq` at all. -/
def SeqStrictMono (B : Lace) : Prop :=
  ∀ a b, Dregg2.Authority.Blocklace.precedes B a b → a.seq < b.seq

/-- Under strict-seq-monotonicity, two strand blocks at the SAME seq are `≺`-incomparable: neither
can precede the other (a precedence would force a strict `<` on equal seqs). -/
theorem same_seq_incomparable {B : Lace} (hsm : SeqStrictMono B)
    {a b : Block} (hseq : a.seq = b.seq) :
    ¬ Dregg2.Authority.Blocklace.precedes B a b ∧
    ¬ Dregg2.Authority.Blocklace.precedes B b a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd (hsm a b h) (by omega)
  · exact absurd (hsm b a h) (by omega)

/-- **`forkFree_of_honestChain`** — the bridge. If `p` follows the honest virtual-chain discipline
(`HonestChain`, from the existing theory), the lace is content-addressed (`Canonical`), and `≺`
strictly increases `seq` (`SeqStrictMono`), then `p`'s strand is fork-free: no two distinct blocks
share a seq. Hence (by §3) `p` has a single tip. An honest author's feed is a single SSB log. -/
theorem forkFree_of_honestChain {B : Lace} {p : AuthorId}
    (hcanon : B.Canonical) (hsm : SeqStrictMono B) (hon : HonestChain B p) :
    StrandForkFree B p := by
  intro a ha b hb hseq
  by_contra hne
  -- a, b are distinct same-seq p-blocks; HonestChain forces them comparable, but same_seq says no.
  have haB := strand_subset ha
  have hbB := strand_subset hb
  have hla : B.lookup a.id = some a :=
    Dregg2.Authority.Blocklace.lookup_of_mem hcanon haB
  have hlb : B.lookup b.id = some b :=
    Dregg2.Authority.Blocklace.lookup_of_mem hcanon hbB
  have hcomp := hon a b hla hlb (strand_creator ha) (strand_creator hb) hne
  have hinc := same_seq_incomparable hsm hseq
  rcases hcomp with hab | hba
  · exact hinc.1 hab
  · exact hinc.2 hba

/-! ## 5. The fixed write path PRESERVES fork-freedom; the OLD overwriting one does NOT.

We model the two write paths as functions on the strand and show the contrast that IS the A1 fix.
* `insertStrandOk b B` — the FIXED path's *accepting* case: the new block `b` is admitted only when
  it does not collide with an existing strand block at `b.seq` (the `find_conflict`/`Equivocation`
  rejection, `lib.rs:402-423`). We model acceptance as a guard and prove acceptance preserves
  fork-freedom.
* `insertOverwrite b B` — the OLD path: append unconditionally (it `self.blocks.insert`ed the fork
  and overwrote `tips`). We exhibit a concrete strand where it DROPS the single-tip guarantee. -/

/-- The FIXED-insert acceptance guard for the strand: `b` may extend `p`'s feed only if no existing
strand block already occupies `b.seq` (else it is an equivocation/regression and is rejected, not
appended to the live tip). Mirrors the `find_conflict`-clear path of `lib.rs::insert`. -/
def StrandAccepts (B : Lace) (p : AuthorId) (b : Block) : Prop :=
  b.creator = p ∧ ∀ a ∈ Strand B p, a.seq = b.seq → a = b

/-- **`insert_preserves_forkFree`** — the FIXED write path preserves the single-feed invariant.
If `p`'s strand is fork-free and `b` is *accepted* (clears the `find_conflict` guard), then the
extended strand `b :: B` is still fork-free. This is the inductive step that makes "every reachable
lace has one tip per honest creator" hold under the corrected `insert`. -/
theorem insert_preserves_forkFree {B : Lace} {p : AuthorId} {b : Block}
    (hff : StrandForkFree B p) (hacc : StrandAccepts B p b) :
    StrandForkFree (b :: B) p := by
  obtain ⟨hbcr, hguard⟩ := hacc
  intro x hx y hy hseq
  -- membership in Strand (b::B) p is `x = b ∨ x ∈ Strand B p` (b is authored by p).
  have hsplit : ∀ z, z ∈ Strand (b :: B) p → z = b ∨ z ∈ Strand B p := by
    intro z hz
    rcases mem_strand_iff.mp hz with ⟨hzmem, hzcr⟩
    rcases List.mem_cons.mp hzmem with rfl | hztl
    · exact Or.inl rfl
    · exact Or.inr (mem_strand_iff.mpr ⟨hztl, hzcr⟩)
  rcases hsplit x hx with rfl | hxB
  · rcases hsplit y hy with rfl | hyB
    · rfl
    · exact (hguard y hyB hseq.symm).symm
  · rcases hsplit y hy with rfl | hyB
    · exact hguard x hxB hseq
    · exact hff x hxB y hyB hseq

/-- The OLD write path: append the block UNCONDITIONALLY (no `find_conflict` guard). This is the
audited `insert` that did `self.blocks.insert(..)` + silently overwrote `tips[creator]`. -/
def insertOverwrite (b : Block) (B : Lace) : Lace := b :: B

/-! ### Non-vacuity + the contrast (`#guard`-checked). A two-author lace; author `9` forks. -/

/-- Honest author `7`, genesis seq 0. -/
def h0 : Block := { id := 0, creator := 7, seq := 0, preds := [] }
/-- Honest author `7`, successor seq 1 (acks `h0`): a clean append-only feed. -/
def h1 : Block := { id := 1, creator := 7, seq := 1, preds := [0] }
/-- Byzantine author `9`, fork branch A at seq 0. -/
def k0a : Block := { id := 2, creator := 9, seq := 0, preds := [] }
/-- Byzantine author `9`, fork branch B at seq 0 — a SECOND block at `(9, 0)`. -/
def k0b : Block := { id := 3, creator := 9, seq := 0, preds := [] }

/-- The honest strand of `7` in the clean lace `[h0, h1]`. -/
def honestLace : Lace := [h0, h1]
/-- A forked lace: the old `insert` would store BOTH `k0a` and `k0b` (the A1 bug).
Built by the OLD unconditional `insertOverwrite` so the contrast is literal:
`insertOverwrite k0b [k0a] = k0b :: [k0a] = [k0b, k0a]`. -/
def forkedLace : Lace := [k0b, k0a]

-- The honest strand has one block per seq (seqs 0 and 1, both distinct).
#guard (Strand honestLace 7).length == 2
#guard decide (h0.seq ≠ h1.seq)
-- The honest feed head is seq 1 (the successor).
#guard strandTipSeq honestLace 7 == 1
-- The forked strand of `9` has TWO blocks at the SAME seq 0 (the dropped fork).
#guard (Strand forkedLace 9).length == 2
#guard decide (k0a.seq = k0b.seq ∧ k0a.id ≠ k0b.id)
#guard strandTipSeq forkedLace 9 == 0

/-- `Strand honestLace 7` reduces to the literal `[h0, h1]` (both blocks are author `7`). -/
theorem strand_honestLace_7 : Strand honestLace 7 = [h0, h1] := by decide

/-- **`honest_strand_forkFree`** — `7`'s strand in `honestLace` is fork-free:
its two blocks sit at distinct seqs, so the single-tip guarantee holds. -/
theorem honest_strand_forkFree : StrandForkFree honestLace 7 := by
  intro a ha b hb hseq
  rw [strand_honestLace_7] at ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | rfl | (exact absurd hseq (by decide))

/-- **`honest_single_tip`** — the honest feed has ONE head: the unique block at its tip
sequence is `h1`. Instantiates the keystone `strand_single_tip` on the concrete clean strand. -/
theorem honest_single_tip {a b : Block}
    (ha : a ∈ Strand honestLace 7) (hb : b ∈ Strand honestLace 7)
    (hatip : a.seq = strandTipSeq honestLace 7) (hbtip : b.seq = strandTipSeq honestLace 7) :
    a = b :=
  strand_single_tip honest_strand_forkFree ha hb hatip hbtip

/-- **`forked_strand_not_forkFree`** — the NEG tooth: the OLD overwriting `insert`
(`insertOverwrite k0b [k0a]` = `forkedLace`) leaves author `9`'s strand NOT fork-free — two
*distinct* blocks `k0a ≠ k0b` both at seq 0. There is no single tip; the fork is live state. This
is precisely the A1 bug the FIXED `insert` repels (it would reject `k0b` as an `Equivocation`,
retaining it only as detectable evidence, never as a second live feed head). -/
theorem forked_strand_not_forkFree :
    forkedLace = insertOverwrite k0b [k0a] ∧ ¬ StrandForkFree forkedLace 9 := by
  refine ⟨rfl, fun hff => ?_⟩
  have hk0b : k0b ∈ Strand forkedLace 9 := by decide
  have hk0a : k0a ∈ Strand forkedLace 9 := by decide
  have : k0b = k0a := hff k0b hk0b k0a hk0a (by decide)
  exact absurd this (by decide)

/-- **`fixed_insert_keeps_single_tip`** — the POSITIVE contrast: extending the clean
honest strand with a fresh seq-2 block via the FIXED accepting path keeps fork-freedom (hence the
single tip). The corrected `insert` admits `h2` (seq 2 clears the `find_conflict` guard) and the
feed stays a single append-only log. -/
theorem fixed_insert_keeps_single_tip :
    StrandForkFree ({ id := 4, creator := 7, seq := 2, preds := [1] } :: honestLace) 7 := by
  apply insert_preserves_forkFree honest_strand_forkFree
  refine ⟨rfl, ?_⟩
  intro a ha hseq
  -- a is in the honest strand (seqs 0,1); the new block is seq 2 — no collision possible,
  -- so the guard hypothesis `a.seq = 2` is contradictory.
  rw [strand_honestLace_7] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> exact absurd hseq (by decide)

/-! ## 6. Connection to finality + the receipt-chain (read-only, hypothesis-level).

The strand tip is the SSB feed head the executor reads; the finalized order
(`BlocklaceFinality.tauOrder`) is computed over the lace whose strands this file constrains. We
record the type-level connection without re-proving finality (it is DONE in `BlocklaceFinality`):
a fork-free strand contributes a single block per `(creator, seq)` to the lace `computeRounds`
folds over, so the round-assignment is well-defined per feed position. The cell's own append-only
receipt chain (`RecordKernel.lean`, owned by another agent) IS a strand of one creator — we state
that as the abstract `StrandForkFree` obligation a well-formed receipt log must satisfy, importing
nothing from `RecordKernel`. -/

/-- **`forkFree_gives_functional_seq`** — a fork-free strand assigns at most one block to each feed
position: `seq ↦ block` is a partial function. This is the well-definedness the finalization round
map and the receipt-chain reader both rely on (each `(creator, seq)` resolves to one block). -/
theorem forkFree_gives_functional_seq {B : Lace} {p : AuthorId} (hff : StrandForkFree B p)
    {a b : Block} (ha : a ∈ Strand B p) (hb : b ∈ Strand B p) (hseq : a.seq = b.seq) :
    a = b := hff a ha b hb hseq

/-- **`receiptChainIsStrand`** — the receipt-chain connection, stated as a definition, not an
import: a cell's append-only receipt log over creator `p` in lace `B` is *well-formed* exactly when
it is a fork-free strand (one receipt per sequence, a single head). The FIXED `insert` is what makes
this hold for every honest cell; `RecordKernel.lean` (another agent's file) provides the receipt
producer, which this predicate constrains read-only. -/
def receiptChainIsStrand (B : Lace) (p : AuthorId) : Prop := StrandForkFree B p

theorem receiptChain_single_head {B : Lace} {p : AuthorId}
    (h : receiptChainIsStrand B p) {a b : Block}
    (ha : a ∈ Strand B p) (hb : b ∈ Strand B p)
    (hatip : a.seq = strandTipSeq B p) (hbtip : b.seq = strandTipSeq B p) :
    a = b := strand_single_tip h ha hb hatip hbtip

/-! ## 7. Axiom hygiene — the strand-integrity model is kernel-clean. -/

#assert_axioms strand_single_tip
#assert_axioms tip_block_exists_unique
#assert_axioms forkFree_of_honestChain
#assert_axioms insert_preserves_forkFree
#assert_axioms forked_strand_not_forkFree
#assert_axioms fixed_insert_keeps_single_tip
#assert_axioms le_strandTipSeq
#assert_axioms forkFree_gives_functional_seq

end Dregg2.Distributed.StrandIntegrity
