/-
# Dregg2.Tree.Spec: the tree certificates composed with the house objects

`Dregg2.Tree` is Lean-core only so that `tree-check` links without Mathlib. This module states
what its pieces ARE in the house vocabulary (the `TableRunSpec` pattern):

* `tableAccepts_eq` / `tableAccepts_dfaAccepts`: the string-leaf check is
  `TableRun.acceptsBytes`, hence (for a non-empty leaf) a `Dfa.lean` accepting run
  (`DfaAccepts`) over the table's δ.
* `leafScheme`: a string leaf's digest is a `Dfa.ContentScheme` over its bytes, and
  `field_accept_bound` delivers exactly the conclusion shape of `Dfa.dfa_bound_verify_sound`
  (`∃ w, commit w = c ∧ ∃ trace, DfaAccepts … ∧ traceWord trace = w`) for `c` the digest of the
  value at the opened path: a field certificate discharges a Layer B′ statement about that leaf.
* `mrootC_eq`: the checker's MMR is `Lightclient.MMR.mroot`.
* ⚑ `corpus_absence`: an accepted corpus certificate with `count = 0`, for ANY named records whose
  digests' MMR root is the statement's, says no record matches the query, or an MMR collision at
  the pair `mrootFind` names, or a collision inside some record's opening or some table encoding.
* `wf_unique_obj`: two objects with strictly sorted keys whose entry lists are permutations of each
  other are equal (one level; the recursive "two spellings, one tree" property of `Json.parse` is
  pinned by `#guard`s, not proved).
-/
import Dregg2.Tree.Instance
import Dregg2.Lightclient.MMR
import Dregg2.Automata.TableRunSpec
import Dregg2.Crypto.Dfa

namespace Dregg2.Tree.Spec

open Dregg2.Tree
open Dregg2.Crypto.Dfa (DfaAccepts ContentScheme traceWord)
open Dregg2.Crypto.Deriv.PredRE (TableDfa)

/-! ## The leaf check is the house DFA -/

def toFlat (t : FlatTable) : Dregg2.Automata.TableRun.FlatTable :=
  { numStates := t.numStates, transitions := t.transitions, start := t.start, accepting := t.accepting }

theorem runFrom_eq (t : FlatTable) (q : Nat) (w : List UInt8) :
    runFrom t q w = Dregg2.Automata.TableRun.runFrom (toFlat t) q w := rfl

theorem tableAccepts_eq (t : FlatTable) (s : List UInt8) :
    tableAccepts t s = Dregg2.Automata.TableRun.acceptsBytes (toFlat t) ⟨s.toArray⟩ := by
  rw [Dregg2.Automata.TableRun.acceptsBytes_eq]
  rfl

/-- The house DFA object of a byte table. -/
def tdOf (t : FlatTable) : TableDfa Nat UInt8 := (toFlat t).toTableDfa

/-- For a non-empty leaf, acceptance is a `Dfa.lean` accepting run reading exactly the leaf. -/
theorem tableAccepts_dfaAccepts (t : FlatTable) (a : UInt8) (as : List UInt8) :
    tableAccepts t (a :: as) = true ↔
      DfaAccepts (tdOf t).δ (tdOf t).start (tdOf t).accept (TableDfa.runTrace (tdOf t) (tdOf t).start (a :: as)) := by
  rw [tableAccepts_eq]
  exact Dregg2.Automata.TableRun.accepts_iff_dfaAccepts (toFlat t) ⟨(a :: as).toArray⟩ a as rfl

theorem traceWord_runTrace (td : TableDfa Nat UInt8) :
    ∀ (q : Nat) (w : List UInt8), traceWord (TableDfa.runTrace td q w) = w
  | _, [] => rfl
  | q, a :: as => by
    simp only [TableDfa.runTrace, Dregg2.Crypto.Dfa.traceWord_cons]
    rw [traceWord_runTrace td _ as]

/-- A string leaf's Merkle digest as a Layer B′ content scheme over the leaf's bytes. -/
def leafScheme (H : List UInt8 → Digest) : ContentScheme UInt8 Digest := ⟨fun w => digest H (.str w)⟩

/-- ⚑ **`field_accept_bound`** — an accepted field certificate with verdict `accept` over a
named record (no collision) gives the Layer B′ conclusion for the leaf at the path: a word that
the leaf scheme commits to the digest of the value there, read by an accepting run. -/
theorem field_accept_bound {H F : List UInt8 → Digest} (hH : HashFits H) (st : FieldStmt)
    (r : FieldReceipt) (acc : fieldCheck H F st r = true) (hv : st.verdict = .accept)
    (t tab : JVal) (ht : TreeAdm t) (htab : Admitted tab)
    (htr : digest H t = st.treeRoot) (hfd : flatDigest F tab = st.tableDigest)
    (hno1 : ¬ Coll H (walkFind H t st.path r.opening)) (hno2 : ¬ Coll F (encode r.table, encode tab)) :
    ∃ T, tableOfJVal tab = some T ∧ ∃ v, lookup t st.path = some v ∧
      ((∃ w, v = .str w ∧ w = [] ∧ tableAccepts T [] = true) ∨
       ∃ w, (leafScheme H).commit w = digest H v ∧
        ∃ trace : List (Dregg2.Crypto.Dfa.Step Nat UInt8),
          DfaAccepts (tdOf T).δ (tdOf T).start (tdOf T).accept trace ∧ traceWord trace = w) := by
  rcases path_pattern_sound hH st r acc t tab ht htab htr hfd with ⟨_, T, hT, hc⟩ | e | e
  · refine ⟨T, hT, ?_⟩
    rw [hv] at hc
    cases hl : lookup t st.path with
    | none => rw [hl] at hc; simp [classify] at hc
    | some v =>
      refine ⟨v, rfl, ?_⟩
      rw [hl] at hc
      cases v with
      | str w =>
        simp only [classify] at hc
        split at hc
        · rename_i hacc
          cases w with
          | nil => exact Or.inl ⟨[], rfl, rfl, hacc⟩
          | cons a as =>
            right
            exact ⟨a :: as, rfl, _, (tableAccepts_dfaAccepts T a as).mp hacc,
              traceWord_runTrace _ _ _⟩
        · cases hc
      | _ => all_goals (simp [classify] at hc)
  · exact absurd e hno1
  · exact absurd e hno2

/-! ## The MMR -/

def toP : PTreeC → Dregg2.Lightclient.MMR.PTree
  | .leaf v => .leaf v
  | .node l r => .node (toP l) (toP r)

theorem height_toP : ∀ t : PTreeC, (toP t).height = t.height
  | .leaf _ => rfl
  | .node l _ => by simp [toP, PTreeC.height, height_toP l]

theorem hashOf_toP (hash : List Int → Int) : ∀ t : PTreeC, (toP t).hashOf hash = t.hashOf hash
  | .leaf _ => rfl
  | .node l r => by simp [toP, PTreeC.hashOf, hashOf_toP hash l, hashOf_toP hash r]

theorem pushC_toP : ∀ (f : List PTreeC) (t : PTreeC),
    (pushC f t).map toP = Dregg2.Lightclient.MMR.push (f.map toP) (toP t)
  | [], t => rfl
  | s :: rest, t => by
    simp only [pushC, List.map_cons, Dregg2.Lightclient.MMR.push_cons, height_toP]
    split
    · rw [pushC_toP rest (.node s t)]; rfl
    · rfl

theorem peaksOfC_toP (L : List Int) :
    (peaksOfC L).map toP = Dregg2.Lightclient.MMR.peaksOf L := by
  unfold peaksOfC Dregg2.Lightclient.MMR.peaksOf
  suffices ∀ (f : List PTreeC), (L.foldl (fun f v => pushC f (.leaf v)) f).map toP =
      L.foldl Dregg2.Lightclient.MMR.appendLeaf (f.map toP) from this []
  induction L with
  | nil => intro f; rfl
  | cons v L ih =>
    intro f
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    exact pushC_toP f (.leaf v)

theorem bagC_toP (hash : List Int → Int) : ∀ f : List PTreeC,
    bagC hash f = Dregg2.Lightclient.MMR.bag hash (f.map toP)
  | [] => rfl
  | t :: rest => by simp [bagC, Dregg2.Lightclient.MMR.bag_cons, hashOf_toP, bagC_toP hash rest]

/-- ⚑ The checker's MMR root IS `Lightclient.MMR.mroot`. -/
theorem mrootC_eq (hash : List Int → Int) (L : List Int) :
    mrootC hash L = Dregg2.Lightclient.MMR.mroot hash L := by
  unfold mrootC Dregg2.Lightclient.MMR.mroot
  rw [bagC_toP, peaksOfC_toP]

/-! ## Leaves: fixed-length digests read big-endian are injective -/

theorem be_ofBE : ∀ l : List UInt8, Cbor.be l.length (Cbor.ofBE l) = l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [List.length_append, List.length_singleton, Cbor.ofBE_append_single]
    simp only [Cbor.be]
    have h1 : (Cbor.ofBE l * 256 + b.toNat) / 256 = Cbor.ofBE l := by
      have := b.toNat_lt; omega
    have h2 : (Cbor.ofBE l * 256 + b.toNat) % 256 = b.toNat := by
      have := b.toNat_lt; omega
    rw [h1, h2, ih]
    simp

theorem leafOf_inj {a b : Digest} (hl : a.length = b.length) (h : leafOf a = leafOf b) : a = b := by
  unfold leafOf at h
  have h' : Cbor.ofBE a = Cbor.ofBE b := by exact_mod_cast h
  rw [← be_ofBE a, ← be_ofBE b, h', hl]

/-- The node hash outputs one length (SHAKE256 at 32 bytes: `shakeH_len`). -/
def HashLen (H : List UInt8 → Digest) (n : Nat) : Prop := ∀ x, (H x).length = n

theorem digest_len {H : List UInt8 → Digest} {n : Nat} (h : HashLen H n) (v : JVal) :
    (digest H v).length = n := by
  cases v <;> simp only [digest] <;> exact h _

theorem map_leafOf_inj {H : List UInt8 → Digest} {n : Nat} (hl : HashLen H n) :
    ∀ (L : List JVal) (ds : List Digest), (∀ d ∈ ds, d.length = n) →
      L.map (fun t => leafOf (digest H t)) = ds.map leafOf → L.map (digest H) = ds
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | t :: L, d :: ds, hd, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨leafOf_inj (by rw [digest_len hl, hd d (by simp)]) h.1,
      map_leafOf_inj hl L ds (fun x hx => hd x (by simp [hx])) h.2⟩

/-! ## ⚑ Corpus absence -/

/-- ⚑ **`corpus_count_mmr`** — an accepted corpus certificate, any count: for any named
records (admitted, whose digests' MMR root is the statement's) and named tables (committed by the
statement), exactly `count` of them match the query; or the MMR collides at the pair `mrootFind` names; or an
opening inside some record, or some table encoding, collides at a computed pair. -/
theorem corpus_count_mmr {H F : List UInt8 → Digest} (hH : HashFits H) (hl : HashLen H 32)
    (hash : List Int → Int) (st : CorpusStmt) (r : CorpusReceipt)
    (acc : corpusCheck H F hash st r = true)
    (L : List JVal) (hL : ∀ t ∈ L, TreeAdm t)
    (hroot : Dregg2.Lightclient.MMR.mroot hash (L.map fun t => leafOf (digest H t)) = st.mmrRoot)
    (tabs : List JVal) (htabs : ∀ x ∈ tabs, Admitted x)
    (htd : tabs.map (flatDigest F) = st.query.map (·.tableDigest)) :
    (∃ Ts, optMap tableOfJVal tabs = some Ts ∧ (L.filter (matchesQ Ts st.query)).length = st.count) ∨
      Dregg2.Lightclient.MMR.MRootColl hash (L.map fun t => leafOf (digest H t))
        (r.records.map fun ev => leafOf ev.root) ∨
      (∃ (i : Nat) (t : JVal) (ev : RecEvidence), L[i]? = some t ∧ r.records[i]? = some ev ∧
        EvColl H st.query t ev) ∨
      (∃ (i : Nat) (a b : JVal), r.tables[i]? = some a ∧ tabs[i]? = some b ∧
        Coll F (encode a, encode b)) := by
  have acc' := acc
  unfold corpusCheck at acc'
  simp only [Bool.and_eq_true, beq_iff_eq] at acc'
  obtain ⟨_, hm⟩ := acc'
  split at hm
  · cases hm
  · simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨_, hall⟩, hmr⟩, _⟩ := hm
    have hrlen : ∀ ev ∈ r.records, ev.root.length = 32 := by
      intro ev hev; simpa using List.all_eq_true.mp hall ev hev
    rw [mrootC_eq] at hmr
    rcases Dregg2.Lightclient.MMR.mroot_binds_or_collides hash (hroot.trans hmr.symm) with e | e
    · have hds : L.map (digest H) = r.records.map (·.root) := by
        apply map_leafOf_inj hl L _ (by simpa using hrlen)
        rw [e, List.map_map]; rfl
      rcases corpus_count_sound hH hash st r acc L hL hds tabs htabs htd with
        ⟨Ts, hTs, hc⟩ | e2 | e2
      · exact Or.inl ⟨Ts, hTs, hc⟩
      · exact Or.inr (Or.inr (Or.inl e2))
      · exact Or.inr (Or.inr (Or.inr e2))
    · exact Or.inr (Or.inl e)

/-- **`corpus_absence`** — an accepted corpus certificate claiming `count = 0`: for any named
records (admitted, whose digests' MMR root is the statement's) and named tables (committed by the
statement), no record matches the query; or the MMR collides at the pair `mrootFind` names; or an
opening inside some record, or some table encoding, collides at a computed pair. -/
theorem corpus_absence {H F : List UInt8 → Digest} (hH : HashFits H) (hl : HashLen H 32)
    (hash : List Int → Int) (st : CorpusStmt) (r : CorpusReceipt)
    (acc : corpusCheck H F hash st r = true) (hzero : st.count = 0)
    (L : List JVal) (hL : ∀ t ∈ L, TreeAdm t)
    (hroot : Dregg2.Lightclient.MMR.mroot hash (L.map fun t => leafOf (digest H t)) = st.mmrRoot)
    (tabs : List JVal) (htabs : ∀ x ∈ tabs, Admitted x)
    (htd : tabs.map (flatDigest F) = st.query.map (·.tableDigest)) :
    (∃ Ts, optMap tableOfJVal tabs = some Ts ∧ ∀ t ∈ L, matchesQ Ts st.query t = false) ∨
      Dregg2.Lightclient.MMR.MRootColl hash (L.map fun t => leafOf (digest H t))
        (r.records.map fun ev => leafOf ev.root) ∨
      (∃ (i : Nat) (t : JVal) (ev : RecEvidence), L[i]? = some t ∧ r.records[i]? = some ev ∧
        EvColl H st.query t ev) ∨
      (∃ (i : Nat) (a b : JVal), r.tables[i]? = some a ∧ tabs[i]? = some b ∧
        Coll F (encode a, encode b)) := by
  have acc' := acc
  unfold corpusCheck at acc'
  simp only [Bool.and_eq_true, beq_iff_eq] at acc'
  obtain ⟨_, hm⟩ := acc'
  split at hm
  · cases hm
  · simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨_, hall⟩, hmr⟩, _⟩ := hm
    have hrlen : ∀ ev ∈ r.records, ev.root.length = 32 := by
      intro ev hev; simpa using List.all_eq_true.mp hall ev hev
    rw [mrootC_eq] at hmr
    rcases Dregg2.Lightclient.MMR.mroot_binds_or_collides hash (hroot.trans hmr.symm) with e | e
    · have hds : L.map (digest H) = r.records.map (·.root) := by
        apply map_leafOf_inj hl L _ (by simpa using hrlen)
        rw [e, List.map_map]; rfl
      rcases corpus_count_sound hH hash st r acc L hL hds tabs htabs htd with
        ⟨Ts, hTs, hc⟩ | e2 | e2
      · left
        refine ⟨Ts, hTs, fun t ht => ?_⟩
        rw [hzero, List.length_eq_zero_iff, List.filter_eq_nil_iff] at hc
        simpa using hc t ht
      · exact Or.inr (Or.inr (Or.inl e2))
      · exact Or.inr (Or.inr (Or.inr e2))
    · exact Or.inr (Or.inl e)

/-! ## The executable instance -/

open Dregg2.Tree.Instance

theorem shakeH_hashLen : HashLen shakeH 32 := shakeH_len

/-- **`corpus_absence` at the deployed hashes** (`tree-check`'s instance): no hypothesis on the
hash remains except the named collisions. -/
theorem corpus_absence_shake (st : CorpusStmt) (r : CorpusReceipt)
    (acc : corpusCheck shakeH flatF mmrHash st r = true) (hzero : st.count = 0)
    (L : List JVal) (hL : ∀ t ∈ L, TreeAdm t)
    (hroot : Dregg2.Lightclient.MMR.mroot mmrHash (L.map fun t => leafOf (digest shakeH t)) = st.mmrRoot)
    (tabs : List JVal) (htabs : ∀ x ∈ tabs, Admitted x)
    (htd : tabs.map (flatDigest flatF) = st.query.map (·.tableDigest)) :
    (∃ Ts, optMap tableOfJVal tabs = some Ts ∧ ∀ t ∈ L, matchesQ Ts st.query t = false) ∨
      Dregg2.Lightclient.MMR.MRootColl mmrHash (L.map fun t => leafOf (digest shakeH t))
        (r.records.map fun ev => leafOf ev.root) ∨
      (∃ (i : Nat) (t : JVal) (ev : RecEvidence), L[i]? = some t ∧ r.records[i]? = some ev ∧
        EvColl shakeH st.query t ev) ∨
      (∃ (i : Nat) (a b : JVal), r.tables[i]? = some a ∧ tabs[i]? = some b ∧
        Coll flatF (encode a, encode b)) :=
  corpus_absence shakeH_fits shakeH_hashLen mmrHash st r acc hzero L hL hroot tabs htabs htd

/-- Lengths of minimal big-endian bytes. -/
theorem natBytes_length_le : ∀ (k n : Nat), n < 256 ^ k → (natBytes n).length ≤ k := by
  intro k
  induction k with
  | zero => intro n hn; simp at hn; subst hn; simp [natBytes]
  | succ k ih =>
    intro n hn
    unfold natBytes
    by_cases h : n = 0
    · simp [h]
    · simp only [h, dite_false, List.length_append, List.length_singleton]
      have := ih (n / 256) (by rw [Nat.pow_succ] at hn; omega)
      omega

theorem adm_intItem {n : Int} (h0 : 0 ≤ n) (h1 : n < 2 ^ 256) : Cbor.Adm (intItem n) := by
  unfold intItem
  rw [if_pos h0]
  split
  · rename_i hlt; simpa [Cbor.Adm] using hlt
  · refine ⟨by decide, ?_⟩
    simp only [Cbor.Adm]
    have h2 : n.toNat < 256 ^ 32 := by
      have : ((256 ^ 32 : Nat) : Int) = 2 ^ 256 := by norm_num
      omega
    have := natBytes_length_le 32 n.toNat h2
    have : (32 : Nat) < 2 ^ 64 := by norm_num
    omega

theorem admList_intItems : ∀ l : List Int, (∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 256) →
    Cbor.AdmList (l.map intItem)
  | [], _ => trivial
  | x :: l, h => ⟨adm_intItem (h x (by simp)).1 (h x (by simp)).2,
      admList_intItems l (fun y hy => h y (by simp [hy]))⟩

theorem map_intItem_inj : ∀ a b : List Int, a.map intItem = b.map intItem → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hx : ofItem (intItem x) = ofItem (intItem y) := by rw [h.1]
    rw [ofItem_intItem, ofItem_intItem] at hx
    simp only [Option.some.injEq, JVal.int.injEq] at hx
    rw [hx, map_intItem_inj a b h.2]

/-- ⚑ **`mmrHash_coll`** — an MMR-hash collision at two distinct lists of 256-bit naturals is a
collision of the truncated SHAKE256 at two distinct inputs (the framing is canonical CBOR). -/
theorem mmrHash_coll {a b : List Int} (h : Dregg2.Circuit.Poseidon2Binding.SpongeColl mmrHash (a, b))
    (ha : ∀ x ∈ a, 0 ≤ x ∧ x < 2 ^ 256) (hb : ∀ x ∈ b, 0 ≤ x ∧ x < 2 ^ 256)
    (hla : a.length ≤ 2) (hlb : b.length ≤ 2) :
    mmrInput a ≠ mmrInput b ∧
      fix32 (Dregg2.Crypto.Keccak.shake256 (mmrInput a) 32) =
        fix32 (Dregg2.Crypto.Keccak.shake256 (mmrInput b) 32) := by
  obtain ⟨hne, heq⟩ := h
  refine ⟨fun e => hne ?_, ?_⟩
  · unfold mmrInput at e
    have e' := List.append_cancel_left e
    have aa : Cbor.Adm (.arr (a.map intItem)) := ⟨by simp; omega, admList_intItems a ha⟩
    have ab : Cbor.Adm (.arr (b.map intItem)) := ⟨by simp; omega, admList_intItems b hb⟩
    have := Cbor.enc_injective aa ab e'
    simp only [Cbor.Item.arr.injEq] at this
    exact map_intItem_inj a b this
  · unfold mmrHash at heq
    exact leafOf_inj (by rw [fix32_length, fix32_length]) heq

/-! ## ⚑ Canonical form is canonical -/

theorem lexLt_irrefl : ∀ a : List UInt8, lexLt a a = false
  | [] => rfl
  | x :: xs => by simp [lexLt, lexLt_irrefl xs]

theorem lexLt_trans : ∀ a b c : List UInt8, lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (UInt8.lt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexLt_trans xs ys zs h1 h2⟩

theorem lexLt_asymm (a b : List UInt8) (h : lexLt a b = true) : lexLt b a = false := by
  cases h2 : lexLt b a
  · rfl
  · have := lexLt_trans a b a h h2; rw [lexLt_irrefl] at this; cases this

theorem keysSorted_pairwise : ∀ kvs : List (List UInt8 × JVal), keysSorted kvs = true →
    kvs.Pairwise (fun x y => keyLt x.1 y.1 = true)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | (a, u) :: (b, v) :: r, h => by
    simp only [keysSorted, Bool.and_eq_true] at h
    have ih := keysSorted_pairwise ((b, v) :: r) h.2
    refine List.Pairwise.cons ?_ ih
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact h.1
    · exact lexLt_trans _ _ _ h.1 (List.rel_of_pairwise_cons ih hy)

/-- **`wf_unique_obj`**: two canonical objects whose entry lists are
permutations of each other (one JSON object, two spellings) are the same list. -/
theorem wf_unique_obj {a b : List (List UInt8 × JVal)} (ha : keysSorted a = true)
    (hb : keysSorted b = true) (hp : a.Perm b) : a = b := by
  have pa := keysSorted_pairwise a ha
  have pb := keysSorted_pairwise b hb
  refine List.Perm.eq_of_pairwise (le := fun x y => keyLt x.1 y.1 = true) ?_ pa pb hp
  intro x y _ _ h1 h2
  unfold keyLt at h1 h2; rw [lexLt_asymm _ _ h1] at h2; cases h2

/-- info: 'Dregg2.Tree.Spec.corpus_absence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms corpus_absence
/-- info: 'Dregg2.Tree.Spec.field_accept_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms field_accept_bound
/-- info: 'Dregg2.Tree.Spec.mrootC_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms mrootC_eq
/-- info: 'Dregg2.Tree.Spec.wf_unique_obj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wf_unique_obj

/-- info: 'Dregg2.Tree.Spec.corpus_absence_shake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms corpus_absence_shake
/-- info: 'Dregg2.Tree.Spec.mmrHash_coll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mmrHash_coll

/-- info: 'Dregg2.Tree.Spec.corpus_count_mmr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms corpus_count_mmr

end Dregg2.Tree.Spec
