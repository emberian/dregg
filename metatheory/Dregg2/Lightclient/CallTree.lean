/-
# Dregg2.Lightclient.CallTree — a verified root certifies the whole call tree.

The definitions (and the function the extracted checker runs) are in `CallTreeCore`; this module
proves what an accepting `verify V hash root t` buys a stranger who holds only `root`.

* **`mrootC_eq`** — the core-only MMR copy IS `MMR.mroot`, so every MMR theorem applies to the
  children roots the checker computes.
* **`commit_binds_or_collides`** — two trees with the same commitment are equal, OR the TOTAL
  extractor `treeFind` names a pair of distinct preimages on which `hash` collides. The extractor is
  the point: `∃ p, SpongeColl hash p` holds for EVERY compressing hash by pigeonhole, so a theorem
  ending in a bare existential would say nothing. Here the pair is computed from the two trees.
* **`verify_sound`** — accept ⇒ every node of the presented tree passes the hop predicate `V`, and
  any tree `t₀` with that root (the one the recorder committed) equals the presented tree or
  `treeFind` names a collision. **`no_omission`** reads it as: no node of `t₀` (no hop, no child, no
  response) is missing, swapped, added or reordered in what the verifier accepted.
* **`verify_attested`** — composed with the transport carrier `TransportSound V Attested` (an
  accepting `V` on a transport hop means the hop's attestation is genuine for its host, request and
  response — what `presentation.verify()` + the notary pin + the digests are trusted to give), every
  transport hop of `t₀` is `Attested`.
* **`deployed_coll_is_blake3_coll`** (§5) — at the deployed `CallTreeDeploy.treeHash`, a collision
  `treeFind` names is a genuine BLAKE3-256 collision of the two encodings (within the 4-byte length
  prefixes' bounds).
* Falsifiers (§4, by compiled evaluation, at a toy hash): a dropped child, a swapped response, a reorder, an
  attestation for a different host, each refused; the honest tree accepted.

What this does NOT prove is listed in `calltree/GROUNDING.md` §6 (liveness, unrecorded calls, timing,
notary honesty, replay).
-/
import Dregg2.Lightclient.CallTreeCore
import Dregg2.Lightclient.CallTreeDeploy
import Dregg2.Lightclient.MMR

namespace Dregg2.Lightclient.CallTree

open Dregg2.Lightclient.CallTreeCore
open Dregg2.Circuit.Poseidon2Binding (SpongeColl)

/-! ## §1 — the core-only MMR is `MMR.mroot`. -/

def toP : PT → MMR.PTree
  | .leaf v => .leaf v
  | .node l r => .node (toP l) (toP r)

theorem height_toP : ∀ t : PT, (toP t).height = t.height
  | .leaf _ => rfl
  | .node l _ => by simp [toP, PT.height, height_toP l]

theorem hashOf_toP (hash : List ℤ → ℤ) : ∀ t : PT, (toP t).hashOf hash = t.hashOf hash
  | .leaf _ => rfl
  | .node l r => by simp [toP, PT.hashOf, hashOf_toP hash l, hashOf_toP hash r]

theorem push_toP : ∀ (f : List PT) (t : PT), (push f t).map toP = MMR.push (f.map toP) (toP t)
  | [], _ => rfl
  | s :: rest, t => by
      simp only [push, List.map_cons, MMR.push, height_toP]
      split
      · rw [push_toP rest (.node s t)]; rfl
      · rfl

theorem peaksOf_toP (L : List ℤ) : (peaksOf L).map toP = MMR.peaksOf L := by
  unfold peaksOf MMR.peaksOf
  suffices h : ∀ (f : List PT) (L : List ℤ),
      (L.foldl appendLeaf f).map toP = L.foldl MMR.appendLeaf (f.map toP) by
    simpa using h [] L
  intro f L
  induction L generalizing f with
  | nil => rfl
  | cons v L ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      exact push_toP f (.leaf v)

theorem bag_toP (hash : List ℤ → ℤ) : ∀ f : List PT, MMR.bag hash (f.map toP) = bag hash f
  | [] => rfl
  | t :: rest => by simp [bag, hashOf_toP, bag_toP hash rest]

/-- **The checker's MMR root is the MMR module's root.** -/
theorem mrootC_eq (hash : List ℤ → ℤ) (L : List ℤ) : mrootC hash L = MMR.mroot hash L := by
  unfold mrootC MMR.mroot
  rw [← peaksOf_toP, bag_toP]

/-! ## §2 — the commitment binds the tree, or a named pair collides. -/

theorem commits_eq_map (hash : List ℤ → ℤ) : ∀ ks : List CallTree, commits hash ks = ks.map (commit hash)
  | [] => by simp [commits]
  | k :: ks => by simp [commits, commits_eq_map hash ks]

theorem commit_eq_hash_preimage (hash : List ℤ → ℤ) (t : CallTree) :
    commit hash t = hash (preimage hash t) := by
  cases t; simp [commit, preimage, kidsRoot]

mutual
/-- **THE TREE-COLLISION EXTRACTOR (TOTAL).** If the two nodes' preimages differ, they are the pair;
else if the children's commitment lists differ, the MMR extractor names the pair; else walk the
children. -/
def treeFind (hash : List ℤ → ℤ) : CallTree → CallTree → List ℤ × List ℤ
  | .node h ks, .node h' ks' =>
      if preimage hash (.node h ks) ≠ preimage hash (.node h' ks') then
        (preimage hash (.node h ks), preimage hash (.node h' ks'))
      else if commits hash ks ≠ commits hash ks' then
        MMR.mrootFind hash (commits hash ks) (commits hash ks')
      else kidsFind hash ks ks'
/-- Walk equal-commitment children pairwise; the first pair whose extractor names a collision. -/
def kidsFind (hash : List ℤ → ℤ) : List CallTree → List CallTree → List ℤ × List ℤ
  | k :: ks, k' :: ks' =>
      if SpongeColl hash (treeFind hash k k') then treeFind hash k k' else kidsFind hash ks ks'
  | _, _ => ([], [])
end

theorem hop_eq_of_fields {h h' : Hop} (e : h.fields = h'.fields) : h = h' := by
  cases h; cases h'; simp [Hop.fields] at e; simp [e]

mutual
/-- **⚑ THE TREE BINDING, UNCONDITIONAL.** Equal commitments force equal trees, OR the pair
`treeFind` returns is a genuine collision of `hash`. No collision-resistance floor is assumed. -/
theorem commit_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ (t t' : CallTree), commit hash t = commit hash t' →
      t = t' ∨ SpongeColl hash (treeFind hash t t')
  | .node h ks, .node h' ks', heq => by
      rw [commit_eq_hash_preimage, commit_eq_hash_preimage] at heq
      by_cases hp : preimage hash (.node h ks) = preimage hash (.node h' ks')
      · simp only [preimage, kidsRoot] at hp
        have hlen : (h.fields).length = (h'.fields).length := by simp [Hop.fields]
        obtain ⟨hf, hr⟩ := List.append_inj hp hlen
        have hroot : mrootC hash (commits hash ks) = mrootC hash (commits hash ks') := by
          simpa using hr
        by_cases hc : commits hash ks = commits hash ks'
        · rcases kids_binds_or_collides hash ks ks' hc with hk | hk
          · exact Or.inl (by rw [hop_eq_of_fields hf, hk])
          · refine Or.inr ?_
            have hp' : preimage hash (.node h ks) = preimage hash (.node h' ks') := by
              simp [preimage, kidsRoot, hf, hc]
            simp only [treeFind, hp', ne_eq, not_true_eq_false, if_false, hc]
            exact hk
        · rw [mrootC_eq, mrootC_eq] at hroot
          rcases MMR.mroot_binds_or_collides hash hroot with hk | hk
          · exact absurd hk hc
          · refine Or.inr ?_
            have hp' : preimage hash (.node h ks) = preimage hash (.node h' ks') := by
              simp [preimage, kidsRoot, hf, mrootC_eq, hroot]
            simp only [treeFind, hp', ne_eq, not_true_eq_false, if_false, hc, not_false_eq_true,
              if_true]
            exact hk
      · refine Or.inr ?_
        simp only [treeFind, ne_eq, hp, not_false_eq_true, if_true]
        exact ⟨hp, heq⟩
/-- The children walk: equal commitment lists force equal child lists, or a named collision. -/
theorem kids_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ (ks ks' : List CallTree), commits hash ks = commits hash ks' →
      ks = ks' ∨ SpongeColl hash (kidsFind hash ks ks')
  | [], [], _ => Or.inl rfl
  | [], _ :: _, h => by simp [commits] at h
  | _ :: _, [], h => by simp [commits] at h
  | k :: ks, k' :: ks', h => by
      simp only [commits, List.cons.injEq] at h
      obtain ⟨hk, hks⟩ := h
      by_cases hcoll : SpongeColl hash (treeFind hash k k')
      · refine Or.inr ?_
        simp only [kidsFind, hcoll, if_true]
      · rcases commit_binds_or_collides hash k k' hk with e | e
        · rcases kids_binds_or_collides hash ks ks' hks with e' | e'
          · exact Or.inl (by rw [e, e'])
          · refine Or.inr ?_
            simp only [kidsFind, hcoll, if_false]
            exact e'
        · exact absurd e hcoll
end

mutual
/-- **The extractor names nothing on an honest pair**: `treeFind hash t t = ([], [])`, which is never a
collision (`SpongeColl` needs distinct inputs). So the residual in every theorem below is absent
whenever the presented tree IS the committed one, for every hash. -/
theorem treeFind_self (hash : List ℤ → ℤ) : ∀ t : CallTree, treeFind hash t t = ([], [])
  | .node h ks => by
      simp only [treeFind, ne_eq, not_true_eq_false, if_false]
      exact kidsFind_self hash ks
theorem kidsFind_self (hash : List ℤ → ℤ) : ∀ ks : List CallTree, kidsFind hash ks ks = ([], [])
  | [] => by simp [kidsFind]
  | k :: ks => by
      have hk := treeFind_self hash k
      have hn : ¬ SpongeColl hash (treeFind hash k k) := by
        rw [hk]; exact fun h => h.1 rfl
      simp only [kidsFind, hn, if_false]
      exact kidsFind_self hash ks
end

theorem treeFind_self_not_coll (hash : List ℤ → ℤ) (t : CallTree) :
    ¬ SpongeColl hash (treeFind hash t t) := by
  rw [treeFind_self]; exact fun h => h.1 rfl

/-! ## §3 — what an accepting verify gives. -/

mutual
/-- Every subtree (each node with its own children), preorder. -/
def nodes : CallTree → List CallTree
  | .node h ks => .node h ks :: nodesL ks
def nodesL : List CallTree → List CallTree
  | [] => []
  | k :: ks => nodes k ++ nodesL ks
end

mutual
theorem allOk_nodes (V : Hop → ℤ → Bool) (hash : List ℤ → ℤ) :
    ∀ t : CallTree, allOk V hash t = true →
      ∀ n ∈ nodes t, V n.hop (kidsRoot hash n.kids) = true
  | .node h ks, hok, n, hn => by
      simp only [allOk, Bool.and_eq_true] at hok
      simp only [nodes, List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact hok.1
      · exact allOkL_nodes V hash ks hok.2 n hn
theorem allOkL_nodes (V : Hop → ℤ → Bool) (hash : List ℤ → ℤ) :
    ∀ ks : List CallTree, allOkL V hash ks = true →
      ∀ n ∈ nodesL ks, V n.hop (kidsRoot hash n.kids) = true
  | [], _, n, hn => by simp [nodesL] at hn
  | k :: ks, hok, n, hn => by
      simp only [allOkL, Bool.and_eq_true] at hok
      simp only [nodesL, List.mem_append] at hn
      rcases hn with hn | hn
      · exact allOk_nodes V hash k hok.1 n hn
      · exact allOkL_nodes V hash ks hok.2 n hn
end

/-- Every node of a tree other than its root. -/
def descendants (t : CallTree) : List CallTree := nodesL t.kids

theorem nodes_eq (t : CallTree) : nodes t = t :: descendants t := by
  cases t; rfl

/-- **⚑ `verify_sound`.** An accepting verify gives (1) every node of the presented tree passes `V`
with its own children root, (2) the root is the local turn node and every other node is a transport
hop, and (3) any tree `t₀` committed under `root` — the recorder's — is the presented tree, or
`treeFind` names a collision of `hash` between them. -/
theorem verify_sound {V : Hop → ℤ → Bool} {hash : List ℤ → ℤ} {root : ℤ} {t : CallTree}
    (hv : verify V hash root t = true) :
    (∀ n ∈ nodes t, V n.hop (kidsRoot hash n.kids) = true) ∧
    t.hop.kind = 0 ∧ (∀ n ∈ descendants t, n.hop.kind ≠ 0) ∧
    ∀ t₀ : CallTree, commit hash t₀ = root → t₀ = t ∨ SpongeColl hash (treeFind hash t₀ t) := by
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  obtain ⟨⟨⟨hroot, hk0⟩, htr⟩, hall⟩ := hv
  refine ⟨allOk_nodes V hash t hall, hk0, fun n hn => ?_, fun t₀ h₀ => ?_⟩
  · have := allOkL_nodes isTransport hash t.kids htr n hn
    simpa [isTransport] using this
  · exact commit_binds_or_collides hash t₀ t (h₀.trans hroot.symm)

/-- **⚑ `no_omission`.** Read off the recorder's tree `t₀`: unless the extractor names a collision,
EVERY node of `t₀` — every hop, with exactly its children in order — is a node of what the verifier
accepted, and passes `V`. A dropped, added, reordered or altered child changes `nodes`. -/
theorem no_omission {V : Hop → ℤ → Bool} {hash : List ℤ → ℤ} {root : ℤ} {t t₀ : CallTree}
    (hv : verify V hash root t = true) (h₀ : commit hash t₀ = root)
    (hnc : ¬ SpongeColl hash (treeFind hash t₀ t)) :
    nodes t₀ = nodes t ∧ ∀ n ∈ nodes t₀, V n.hop (kidsRoot hash n.kids) = true := by
  obtain ⟨hall, _, _, hbind⟩ := verify_sound hv
  rcases hbind t₀ h₀ with e | e
  · subst e; exact ⟨rfl, hall⟩
  · exact absurd e hnc

/-- **The transport carrier**, named and not proved: an accepting `V` on a transport hop `h` with
children root `r` means its attestation is genuine for its host, request and response — and, for a
hop to a recording callee (kind 2), that the authenticated response carries `r`, so the callee's
subtree is bound by the caller's attestation. In deployment `V` checks digests and pins
over what `presentation.verify()` extracted; that extraction and the notary's honesty are the trust. -/
def TransportSound (V : Hop → ℤ → Bool) (Attested : Hop → ℤ → Prop) : Prop :=
  ∀ h r, V h r = true → h.kind ≠ 0 → Attested h r

/-- **⚑ `verify_attested`.** Accept + the carrier ⇒ EVERY node of the recorder's tree other than
its root is a transport hop and is attested, unless the extractor names a collision. -/
theorem verify_attested {V : Hop → ℤ → Bool} {Attested : Hop → ℤ → Prop} {hash : List ℤ → ℤ}
    {root : ℤ} {t t₀ : CallTree} (hT : TransportSound V Attested)
    (hv : verify V hash root t = true) (h₀ : commit hash t₀ = root) :
    (∀ n ∈ descendants t₀, n.hop.kind ≠ 0 ∧ Attested n.hop (kidsRoot hash n.kids)) ∨
      SpongeColl hash (treeFind hash t₀ t) := by
  by_cases hc : SpongeColl hash (treeFind hash t₀ t)
  · exact Or.inr hc
  · obtain ⟨_, _, hkinds, hbind⟩ := verify_sound hv
    obtain ⟨hn, hall⟩ := no_omission hv h₀ hc
    rcases hbind t₀ h₀ with e | e
    · subst e
      refine Or.inl fun n hn' => ⟨hkinds n hn', ?_⟩
      have hmem : n ∈ nodes t₀ := by rw [nodes_eq]; exact List.mem_cons_of_mem _ hn'
      exact hT _ _ (hall n hmem) (hkinds n hn')
    · exact absurd e hc

/-! ## §4 — falsifiers and the honest witness, at a toy hash.

Facts about CONCRETE data are checked by compiled evaluation (`native_decide`, pinned with
`#assert_compiled`: they rest on `Lean.ofReduceBool`, i.e. Lean's compiler is trusted), per ember's
standing policy; the general theorems above stay kernel-proved (`#assert_axioms`). -/

namespace Demo

/-- A toy hash: deterministic, NOT collision resistant — the falsifiers below are refused by `V` or
by the root moving, never by a property of this function. -/
def toyHash (xs : List ℤ) : ℤ := xs.foldl (fun a x => a * 1000003 + x) (17 + xs.length)

/-- The authenticated extracts the transport verifier produced, keyed by attestation digest:
`att ↦ (host, req, resp)`. Host 7 = the LLM host, 8 = the tool host, 9 = an unrelated host. -/
def ext : ℤ → Option (ℤ × ℤ × ℤ)
  | 101 => some (7, 1, 2)
  | 102 => some (8, 3, 4)
  | 103 => some (7, 5, 6)
  | 104 => some (7, 3, 4)
  | 105 => some (9, 3, 4)
  | _ => none

def allowed (host : ℤ) : Bool := host == 7 || host == 8

/-- The demo hop predicate: a local node passes; a transport hop passes iff its attestation's
authenticated extract is exactly the hop's (host, req, resp) and the host is allowed. -/
def V (h : Hop) (_kr : ℤ) : Bool :=
  if h.kind = 0 then true else
  match ext h.att with
  | some (ho, q, s) => ho == h.host && q == h.req && s == h.resp && allowed ho
  | none => false

def llm1 : CallTree := .node ⟨1, 101, 7, 1, 2⟩ []
def tool : CallTree := .node ⟨1, 102, 8, 3, 4⟩ []
def llm2 : CallTree := .node ⟨1, 103, 7, 5, 6⟩ []
def turn : CallTree := .node ⟨0, 0, 0, 11, 12⟩ [llm1, tool, llm2]
def root : ℤ := commit toyHash turn

/-- The honest tree is accepted (non-vacuity). -/
theorem honest_accepted : verify V toyHash root turn = true := by native_decide

/-- A dropped child (the tool call) is refused: the root moves. -/
theorem dropped_child_refused :
    verify V toyHash root (.node ⟨0, 0, 0, 11, 12⟩ [llm1, llm2]) = false := by native_decide

/-- Reordered children are refused. -/
theorem reordered_refused :
    verify V toyHash root (.node ⟨0, 0, 0, 11, 12⟩ [tool, llm1, llm2]) = false := by native_decide

/-- A swapped response, re-committed by the forger so the ROOT matches, is refused by `V`: the
attested response is 4, the node claims 99. -/
theorem swapped_response_refused :
    let t := CallTree.node ⟨0, 0, 0, 11, 12⟩ [llm1, .node ⟨1, 102, 8, 3, 99⟩ [], llm2]
    verify V toyHash (commit toyHash t) t = false := by native_decide

/-- An attestation for a DIFFERENT, ALSO ALLOWED host (att 104 authenticated the LLM host 7, with the
tool hop's very request and response digests) presented under the tool host's name 8, re-committed
so the root matches, is refused — by the host comparison alone (the allowlist admits 7). -/
theorem other_host_refused :
    let t := CallTree.node ⟨0, 0, 0, 11, 12⟩ [llm1, .node ⟨1, 104, 8, 3, 4⟩ [], llm2]
    verify V toyHash (commit toyHash t) t = false := by native_decide

/-- The same attestation presented honestly under its own host is refused by the host policy. -/
theorem unlisted_host_refused :
    let t := CallTree.node ⟨0, 0, 0, 11, 12⟩ [llm1, .node ⟨1, 105, 9, 3, 4⟩ [], llm2]
    verify V toyHash (commit toyHash t) t = false := by native_decide

/-- A transport hop RELABELLED as local (kind 0, so `V` would wave it through), re-committed so the
root matches, is refused by the structural rule: only the root may be local. -/
theorem relabelled_local_refused :
    let t := CallTree.node ⟨0, 0, 0, 11, 12⟩ [llm1, .node ⟨0, 0, 0, 3, 4⟩ [], llm2]
    verify V toyHash (commit toyHash t) t = false := by native_decide

end Demo

/-! ## §5 — At the deployed hash, a named collision is a BLAKE3 collision.

`CallTreeDeploy.treeHash_coll_is_blake3_coll` (proved core-only, beside the definitions the checker
runs), read at the `SpongeColl` the extractor `treeFind` names: within the encoding's bounds (list
length and each element's magnitude byte-count below `2^32`), the pair's encodings are distinct
BLAKE3 inputs with one BLAKE3 output. -/

theorem deployed_coll_is_blake3_coll {p : List ℤ × List ℤ}
    (h : SpongeColl CallTreeDeploy.treeHash p)
    (h1l : p.1.length < 2 ^ 32) (h2l : p.2.length < 2 ^ 32)
    (h1 : ∀ x ∈ p.1, (CallTreeDeploy.natBE x.natAbs).size < 2 ^ 32)
    (h2 : ∀ y ∈ p.2, (CallTreeDeploy.natBE y.natAbs).size < 2 ^ 32) :
    CallTreeDeploy.encList p.1 ≠ CallTreeDeploy.encList p.2 ∧
      Dregg2.Crypto.Blake3.hash (CallTreeDeploy.encList p.1) =
        Dregg2.Crypto.Blake3.hash (CallTreeDeploy.encList p.2) :=
  CallTreeDeploy.treeHash_coll_is_blake3_coll h.1 h.2 h1l h2l h1 h2

#assert_axioms mrootC_eq
#assert_axioms commit_binds_or_collides
#assert_axioms verify_sound
#assert_axioms no_omission
#assert_axioms verify_attested
#assert_axioms treeFind_self
#assert_axioms treeFind_self_not_coll
#assert_compiled Demo.honest_accepted
#assert_compiled Demo.dropped_child_refused
#assert_compiled Demo.reordered_refused
#assert_compiled Demo.swapped_response_refused
#assert_compiled Demo.other_host_refused
#assert_compiled Demo.unlisted_host_refused
#assert_compiled Demo.relabelled_local_refused
#assert_axioms Dregg2.Crypto.Blake3.hash_size
#assert_axioms CallTreeDeploy.ofBE_natBE
#assert_axioms CallTreeDeploy.ofBE_injective_of_size
#assert_axioms CallTreeDeploy.encList_injective
#assert_axioms CallTreeDeploy.treeHash_coll_is_blake3_coll
#assert_axioms deployed_coll_is_blake3_coll

end Dregg2.Lightclient.CallTree
