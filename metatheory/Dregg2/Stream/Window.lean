/-
# Dregg2.Stream.Window: window receipts compose, and the composed chain inherits non-omission

`Core.Policy.checkWindow` checks one window against the follower's previous state; this file proves
what an accepted window, and an accepted chain of windows, means.

* `hfront_append` / `hbag_hfront`: `Core.hpush` / `Core.hbag` are `Lightclient.MMR.push` / `bag` with
  every tree replaced by `(height, hashOf)`. So the follower's O(log n) frontier computes the very
  `mroot` the MMR theory is about, with no hash assumption.
* `Tracks P log acc`: the follower state `acc` is the monitor run, the frontier and the root of `log`.
* **`window_sound`**: if the follower `Tracks log acc` and accepts receipt `c` for window `ws`, then the
  follower now tracks `log ++ ws`, and `c` states exactly: positions `[|log|, |log| + |ws|)`, the root
  before and after (`mroot` of the two logs), the state before and after (the automaton's run on the
  committed symbols), the counters, the verdict, and that the window is the dense range
  `[n0, n1)` of the new log.
* **`windows_compose`**: a chain accepted from genesis tracks the concatenated log; for every infinite
  extension `σ` of its symbols, the final state and counter are `run σ n` and `marks σ n`, and
  `lastMark` is the last marked position (0 = none); a `viol`
  verdict means every extension is rejected; and any range answer, against any log recomposing the
  final root, is exactly the monitored log's range with every position present
  (`Lightclient.MMR.server_cannot_omit_position`), unless the server found the named sponge collision.
* **`anchored_is_genuine`**: if the final root equals a root published for a log `L`, the monitored
  values ARE `L` (modulo `MRootColl`). **`anchored_entries_genuine`**: for genuine entries `G`, the
  monitored entries and their symbols ARE `G`'s, modulo `MRootColl` or a named entry-digest collision. The chain check alone ties receipts to the windows it is shown;
  this is what ties them to the source.
* `chain_append` (prefix monotonicity: a chain's prefix is an accepted chain, and its windows' ranges
  stay verbatim in the longer log), `chain_verdict_final` (a `viol` window is followed only by `viol`).
* Falsifiers at a toy policy: a dropped position is refused and moves the root; a dropped VIOLATING
  position would flip the verdict and is caught by the root; swapped windows are refused.

Hypotheses: the verdict certificate's `Valid` (checked per policy) and the per-instance `¬ MRootColl`
residual; nothing else. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Stream.Omega

namespace Dregg2.Stream

open Dregg2.Lightclient.MMR

/-! ## The hashed frontier is the MMR's -/

/-- A tree's frontier entry. -/
def peakAbs (hash : List ℤ → ℤ) (t : PTree) : HPeak := (t.height, t.hashOf hash)

/-- The hashed frontier of a log. -/
def hfront (hash : List ℤ → ℤ) (L : List ℤ) : List HPeak := (peaksOf L).map (peakAbs hash)

theorem hpush_abs (hash : List ℤ → ℤ) :
    ∀ (f : Forest) (t : PTree), (push f t).map (peakAbs hash) = hpush hash (f.map (peakAbs hash)) (peakAbs hash t)
  | [], t => rfl
  | s :: rest, t => by
    rw [push_cons]
    by_cases h : t.height = s.height
    · rw [if_pos h, hpush_abs hash rest (.node s t)]
      simp only [List.map_cons, hpush, peakAbs, h, if_true]
      rfl
    · rw [if_neg h]
      simp [hpush, peakAbs, h]

theorem hfront_nil (hash : List ℤ → ℤ) : hfront hash [] = [] := rfl

/-- **The follower's O(1)-amortized frontier update is the MMR append.** -/
theorem hfront_append (hash : List ℤ → ℤ) (L : List ℤ) (v : ℤ) :
    hfront hash (L ++ [v]) = happend hash (hfront hash L) v := by
  rw [hfront, peaksOf_append, hpush_abs]
  rfl

theorem hfront_appendList (hash : List ℤ → ℤ) (L : List ℤ) :
    ∀ M : List ℤ, hfront hash (L ++ M) = M.foldl (happend hash) (hfront hash L)
  | [] => by simp
  | v :: M => by
    rw [show L ++ v :: M = (L ++ [v]) ++ M by simp, hfront_appendList hash (L ++ [v]) M,
      hfront_append]
    rfl

theorem hbag_abs (hash : List ℤ → ℤ) : ∀ f : Forest, hbag hash (f.map (peakAbs hash)) = bag hash f
  | [] => rfl
  | t :: f => by simp [hbag, bag, peakAbs, hbag_abs hash f]

/-- **The bagged frontier is the MMR root.** -/
theorem hbag_hfront (hash : List ℤ → ℤ) (L : List ℤ) : hbag hash (hfront hash L) = mroot hash L :=
  hbag_abs hash _

/-! ## Tracking -/

variable {E Q Sym : Type}

/-- The follower state is the monitor, frontier and root of `log`. -/
def Tracks (P : Policy E Q Sym) (log : List E) (acc : Acc Q) : Prop :=
  acc.st = P.A.scan P.A.init (log.map P.sym) ∧ acc.front = hfront P.hash (log.map P.val) ∧
    acc.root = mroot P.hash (log.map P.val)

theorem genesis_tracks (P : Policy E Q Sym) : Tracks P [] P.genesis := ⟨rfl, rfl, rfl⟩

theorem advance_tracks (P : Policy E Q Sym) {log : List E} {acc : Acc Q} (h : Tracks P log acc)
    (ws : List E) : Tracks P (log ++ ws) (P.advance acc ws) := by
  obtain ⟨h1, h2, _⟩ := h
  have hf : (ws.map P.val).foldl (happend P.hash) acc.front = hfront P.hash ((log ++ ws).map P.val) := by
    rw [h2, List.map_append, hfront_appendList]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Policy.advance, h1, List.map_append, DOmega.scan_append]
  · simp only [Policy.advance, hf]
  · simp only [Policy.advance, hf, hbag_hfront]

theorem tracks_pos (P : Policy E Q Sym) {log : List E} {acc : Acc Q} (h : Tracks P log acc) :
    acc.st.pos = log.length := by
  rw [h.1, DOmega.scan_pos]; simp [DOmega.init]

theorem tracks_q (P : Policy E Q Sym) {log : List E} {acc : Acc Q} (h : Tracks P log acc) :
    acc.st.q = P.A.exec P.A.start (log.map P.sym) := by
  rw [h.1, DOmega.scan_q]; rfl

/-- The window is the dense range `[|A|, |A| + |B|)` of `A ++ B`. -/
theorem mrange_window (A B : List ℤ) : mrange (A ++ B) A.length (A.length + B.length - 1) = B := by
  unfold mrange
  rcases B with _ | ⟨b, B⟩
  · simp only [List.append_nil, List.length_nil, Nat.add_zero]
    rcases A with _ | ⟨a, A⟩
    · rfl
    · simp
  · rw [List.take_of_length_le (by simp; omega)]
    simp

/-- **`window_sound`.** An accepted receipt, after a follower that tracks `log`, states exactly the
automaton's run over the committed window and the MMR range it occupies. -/
theorem window_sound [DecidableEq Q] (P : Policy E Q Sym) {log ws : List E} {acc : Acc Q}
    {c : WindowCert Q} (h : Tracks P log acc) (hc : P.checkWindow acc ws c = true) :
    Tracks P (log ++ ws) (P.advance acc ws) ∧
    c.n0 = log.length ∧ c.n1 = log.length + ws.length ∧
    c.rootIn = mroot P.hash (log.map P.val) ∧ c.rootOut = mroot P.hash ((log ++ ws).map P.val) ∧
    c.stateIn = P.A.exec P.A.start (log.map P.sym) ∧ c.stateOut = P.A.exec c.stateIn (ws.map P.sym) ∧
    c.countIn = acc.st.count ∧ c.countOut = (P.advance acc ws).st.count ∧
    c.frontOut = hfront P.hash ((log ++ ws).map P.val) ∧
    c.verdict = verdictOf P.vc c.stateOut ∧
    mrange ((log ++ ws).map P.val) c.n0 (c.n1 - 1) = ws.map P.val := by
  have hc' : c = P.produce acc ws := by simpa [Policy.checkWindow] using hc
  have ht := advance_tracks P h ws
  have hp := tracks_pos P h
  have hp' := tracks_pos P ht
  have hq := tracks_q P h
  have hq' := tracks_q P ht
  subst hc'
  refine ⟨ht, hp, ?_, h.2.2, ht.2.2, hq, ?_, rfl, rfl, ht.2.1, rfl, ?_⟩
  · simpa [Policy.produce] using hp'
  · simp only [Policy.produce, hq', hq, List.map_append, DOmega.exec_append]
  · simp only [Policy.produce, hp, hp', List.length_append, List.map_append]
    have := mrange_window (log.map P.val) (ws.map P.val)
    simpa using this

/-! ## Chains -/

/-- A chain accepted from a tracked state tracks the concatenation of its windows. -/
theorem chain_tracks [DecidableEq Q] (P : Policy E Q Sym) :
    ∀ (W : List (List E × WindowCert Q)) {log : List E} {acc acc' : Acc Q},
      Tracks P log acc → P.checkChain acc W = some acc' → Tracks P (log ++ W.flatMap Prod.fst) acc'
  | [], log, acc, acc', h, hc => by
    simp [Policy.checkChain] at hc; subst hc; simpa using h
  | (ws, c) :: rest, log, acc, acc', h, hc => by
    simp only [Policy.checkChain] at hc
    split at hc
    · have := chain_tracks P rest (advance_tracks P h ws) hc
      simpa [List.append_assoc] using this
    · cases hc

/-- **Prefix monotonicity.** An accepted chain splits into an accepted prefix chain and an accepted
continuation from the prefix's follower state. -/
theorem chain_append [DecidableEq Q] (P : Policy E Q Sym) :
    ∀ (W W' : List (List E × WindowCert Q)) {acc acc' : Acc Q},
      P.checkChain acc (W ++ W') = some acc' →
      ∃ mid, P.checkChain acc W = some mid ∧ P.checkChain mid W' = some acc'
  | [], W', acc, acc', h => ⟨acc, rfl, by simpa using h⟩
  | (ws, c) :: rest, W', acc, acc', h => by
    simp only [List.cons_append, Policy.checkChain] at h
    split at h
    · obtain ⟨mid, h1, h2⟩ := chain_append P rest W' h
      exact ⟨mid, by simp only [Policy.checkChain]; rw [if_pos ‹_›]; exact h1, h2⟩
    · cases h

/-- **`windows_compose`.** A chain of receipts accepted from genesis is a certificate about the whole
log `W.flatMap Prod.fst`: the follower tracks it; for every infinite extension `σ` of its symbols the
final state and counter are the infinite run's; a `viol` verdict means every extension is rejected
under the stated acceptance condition; and every range answer against any log recomposing the final
root is the monitored log's exact range, every position present, unless the server found the
collision `MRootColl` names. -/
theorem windows_compose [DecidableEq Q] (P : Policy E Q Sym) {cond : Cond} (hv : P.vc.Valid P.A cond)
    {W : List (List E × WindowCert Q)} {acc : Acc Q} (hc : P.checkChain P.genesis W = some acc) :
    let log := W.flatMap Prod.fst
    Tracks P log acc ∧
    (∀ σ : OWord Sym, Extends σ (log.map P.sym) →
        acc.st.q = P.A.run σ log.length ∧ acc.st.count = P.A.marks σ log.length ∧
        (0 < acc.st.lastMark → P.A.mark (P.A.run σ acc.st.lastMark) = true) ∧
        (∀ i, acc.st.lastMark < i → i ≤ log.length → P.A.mark (P.A.run σ i) = false)) ∧
    (verdictOf P.vc acc.st.q = .viol → BadPrefix (P.A.Accepts cond) (log.map P.sym)) ∧
    (verdictOf P.vc acc.st.q = .sat → GoodPrefix (P.A.Accepts cond) (log.map P.sym)) ∧
    (∀ (L' : List ℤ) (lo hi : ℕ) (vals : List ℤ), mroot P.hash L' = acc.root →
        ¬ MRootColl P.hash L' (log.map P.val) → RVerifies L' lo hi vals →
        vals = mrange (log.map P.val) lo hi ∧
        ∀ i, lo ≤ i → i ≤ hi → i < log.length →
          ∃ v, vals[i - lo]? = some v ∧ Opens (log.map P.val) i v) := by
  intro log
  have ht : Tracks P log acc := by simpa using chain_tracks P W (genesis_tracks P) hc
  have hq := tracks_q P ht
  refine ⟨ht, fun σ hσ => ?_, fun h => verdict_viol_sound hv (by rw [← hq]; exact h),
    fun h => verdict_sat_sound hv (by rw [← hq]; exact h), fun L' lo hi vals hroot hno hrv => ?_⟩
  · have := P.A.scan_extends hσ
    rw [List.length_map] at this
    have hp : prefixOf σ log.length = log.map P.sym := by
      have := extends_prefixOf hσ; rwa [List.length_map] at this
    have hlm := P.A.lastMark_marked σ log.length
    have hls := P.A.lastMark_spec σ log.length
    rw [hp] at hlm hls
    rw [ht.1]
    exact ⟨this.1, this.2.2, hlm, hls⟩
  · have hroot' : mroot P.hash L' = mroot P.hash (log.map P.val) := by rw [hroot, ht.2.2]
    have := server_cannot_omit_position P.hash hroot' hno hrv
    refine ⟨this.1, fun i h1 h2 h3 => this.2 i h1 h2 (by simpa using h3)⟩

/-- **Anchored: the follower monitored THE published log.** If the root the follower ends at equals a
root published for a log `L` (by the log's owner, out of band), then the values the follower monitored
are exactly `L`, unless the server found the collision `MRootColl` names. A producer that drops,
inserts or reorders an entry before cutting windows is caught here, not by the chain check (the chain
check only ties receipts to the windows it is shown). -/
theorem anchored_is_genuine [DecidableEq Q] (P : Policy E Q Sym) {W : List (List E × WindowCert Q)}
    {acc : Acc Q} (hc : P.checkChain P.genesis W = some acc) {L : List ℤ}
    (hR : mroot P.hash L = acc.root) (hno : ¬ MRootColl P.hash ((W.flatMap Prod.fst).map P.val) L) :
    (W.flatMap Prod.fst).map P.val = L := by
  have ht : Tracks P (W.flatMap Prod.fst) acc := by simpa using chain_tracks P W (genesis_tracks P) hc
  exact (mroot_binds_or_collides P.hash (ht.2.2.symm.trans hR.symm)).resolve_right hno

/-- Two lists with equal images under `f` are equal, or a position NAMES two distinct elements `f`
identifies. -/
theorem map_eq_or_coll {α : Type} (f : α → ℤ) :
    ∀ (l g : List α), l.map f = g.map f →
      l = g ∨ ∃ (i : ℕ) (a b : α), l[i]? = some a ∧ g[i]? = some b ∧ a ≠ b ∧ f a = f b
  | [], [], _ => Or.inl rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: g, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    by_cases hab : a = b
    · subst hab
      rcases map_eq_or_coll f l g h.2 with he | ⟨i, x, y, hx, hy, hne, hf⟩
      · exact Or.inl (by rw [he])
      · exact Or.inr ⟨i + 1, x, y, by simpa using hx, by simpa using hy, hne, hf⟩
    · exact Or.inr ⟨0, a, b, rfl, rfl, hab, h.1⟩

/-- **Anchored, at the level of entries and symbols.** If the chain's final root is the root published
for the genuine entries `G`, then the monitored entries ARE `G`, so the monitored symbols are `G`'s
symbols, unless one of two NAMED residuals holds: the MMR collision `MRootColl`, or an entry-digest
collision at a named position (two distinct entries with the same committed value, a blake3 collision
for the deployed `entryVal`). -/
theorem anchored_entries_genuine [DecidableEq Q] (P : Policy E Q Sym) {W : List (List E × WindowCert Q)}
    {acc : Acc Q} (hc : P.checkChain P.genesis W = some acc) {G : List E}
    (hR : mroot P.hash (G.map P.val) = acc.root)
    (hno : ¬ MRootColl P.hash ((W.flatMap Prod.fst).map P.val) (G.map P.val)) :
    (W.flatMap Prod.fst = G ∧ (W.flatMap Prod.fst).map P.sym = G.map P.sym) ∨
      ∃ (i : ℕ) (a b : E), (W.flatMap Prod.fst)[i]? = some a ∧ G[i]? = some b ∧ a ≠ b ∧ P.val a = P.val b := by
  rcases map_eq_or_coll P.val _ _ (anchored_is_genuine P hc hR hno) with he | hcoll
  · exact Or.inl ⟨he, by rw [he]⟩
  · exact Or.inr hcoll

/-- **A `viol` window is followed only by `viol` windows**: if the chain's prefix ends `viol`, so does
the whole chain. -/
theorem chain_verdict_final [DecidableEq Q] (P : Policy E Q Sym) {cond : Cond} (hv : P.vc.Valid P.A cond)
    {W W' : List (List E × WindowCert Q)} {mid acc : Acc Q}
    (h1 : P.checkChain P.genesis W = some mid) (h2 : P.checkChain mid W' = some acc)
    (hviol : verdictOf P.vc mid.st.q = .viol) : verdictOf P.vc acc.st.q = .viol := by
  have ht1 := chain_tracks P W (genesis_tracks P) h1
  have ht2 := chain_tracks P W' ht1 h2
  rw [tracks_q P ht1] at hviol
  rw [tracks_q P ht2, List.map_append]
  exact verdict_viol_final hv _ _ (by simpa using hviol)

/-- Earlier windows' ranges survive later appends verbatim (`append_preserves_range`). -/
theorem window_range_persists (L M : List ℤ) {lo hi : ℕ} (hhi : hi < L.length) :
    mrange (L ++ M) lo hi = mrange L lo hi := append_preserves_range L M hhi

#assert_axioms hpush_abs
#assert_axioms hfront_append
#assert_axioms hfront_appendList
#assert_axioms hbag_hfront
#assert_axioms advance_tracks
#assert_axioms mrange_window
#assert_axioms window_sound
#assert_axioms chain_tracks
#assert_axioms chain_append
#assert_axioms windows_compose
#assert_axioms chain_verdict_final
#assert_axioms anchored_is_genuine
#assert_axioms map_eq_or_coll
#assert_axioms anchored_entries_genuine

/-! ## Falsifiers at a toy policy

`toyP`: entries are integers, committed as themselves; the automaton trips on `9` (a safety monitor:
state `true` = tripped, absorbing, unmarked; Büchi over "not tripped"). The hash is a toy polynomial;
the falsifiers do not need it to be collision-free, only to be computed. Facts about these concrete
streams and their hashes are checked by compiled evaluation (`native_decide`, pinned with
`#assert_compiled`, so `Lean.ofReduceBool` is in their axiom set and nowhere else); the general
theorems above stay kernel-proved. -/

def toyHash (l : List ℤ) : ℤ := l.foldl (fun a x => a * 1000003 + x) (l.length + 17 : ℤ)

def toyA : DOmega Bool ℤ where
  step q a := q || decide (a = 9)
  start := false
  mark q := !q

def toyP : Policy ℤ Bool ℤ where
  A := toyA
  vc := ⟨fun q => q, fun _ => false⟩
  hash := toyHash
  val := id
  sym := id

theorem toyP_valid : toyP.vc.Valid toyP.A .buchi := by
  refine ⟨?_, ?_, ?_⟩
  · intro q a h; simp [toyP, toyA] at h ⊢; simp [h]
  · intro q a h; simp [toyP] at h
  · exact ⟨fun q h => by simp [toyP, toyA] at h ⊢; exact h, fun q h => by simp [toyP] at h⟩

/-- Honest receipt for the window `[1, 2, 3]`. -/
def cHonest : WindowCert Bool := toyP.produce toyP.genesis [1, 2, 3]

/-- **Dropped position, refused**: the server ships `[1, 3]` against the honest receipt. -/
theorem falsifier_dropped_refused : toyP.checkWindow toyP.genesis [1, 3] cHonest = false := by native_decide

/-- **Dropped position, self-consistent receipt**: a receipt recomputed over `[1, 3]` is internally
fine but ends at a different root, so a follower anchored to the published root refuses it. -/
theorem falsifier_dropped_moves_root :
    (toyP.produce toyP.genesis [1, 3]).rootOut ≠ cHonest.rootOut := by native_decide

/-- **Dropping the violating entry would flip the verdict**, which is exactly why the root must catch
it: the honest window `[1, 9, 2]` is `viol`, the window without `9` is `unknown`, and their roots
differ. -/
theorem falsifier_dropped_violation :
    (toyP.produce toyP.genesis [1, 9, 2]).verdict = .viol ∧
    (toyP.produce toyP.genesis [1, 2]).verdict = .unknown ∧
    (toyP.produce toyP.genesis [1, 2]).rootOut ≠ (toyP.produce toyP.genesis [1, 9, 2]).rootOut := by
  native_decide

def w1 : List ℤ := [1, 2]
def w2 : List ℤ := [3]
def c1 : WindowCert Bool := toyP.produce toyP.genesis w1
def c2 : WindowCert Bool := toyP.produce (toyP.advance toyP.genesis w1) w2

/-- The honest chain is accepted (non-vacuity of `windows_compose`'s hypothesis). -/
theorem honest_chain_accepted : (toyP.checkChain toyP.genesis [(w1, c1), (w2, c2)]).isSome = true := by
  native_decide

/-- **Swapped windows, refused.** -/
theorem falsifier_swapped_refused : toyP.checkChain toyP.genesis [(w2, c2), (w1, c1)] = none := by native_decide

/-- **Re-chunking is not a different log**: the same entries in other window boundaries end at the same
root and state (the receipts are about the log, not about the chunking). -/
theorem rechunk_same_root :
    (toyP.advance toyP.genesis [1, 2, 3]).root = (toyP.advance (toyP.advance toyP.genesis w1) w2).root := by
  native_decide

#assert_axioms toyP_valid
#assert_compiled falsifier_dropped_refused
#assert_compiled falsifier_dropped_moves_root
#assert_compiled falsifier_dropped_violation
#assert_compiled honest_chain_accepted
#assert_compiled falsifier_swapped_refused
#assert_compiled rechunk_same_root

end Dregg2.Stream
