/-
# Dregg2.Tree.Automaton: deterministic bottom-up tree automata over `JVal`, run certificates, counts

The object of `docs/automata/07-tree-automata.md` §1, on the projected model: a deterministic
bottom-up **hedge** automaton. A scalar gets its state from `leaf`; an array or object runs one
horizontal automaton over its children's states (an object's step also reads the child's key)
from `hstart kind` and finishes with `hfinal kind`. `none` anywhere is rejection.

Objects are ordered here because canonical objects are (`Value.WF`: keys sorted by encoded bytes,
RFC 8949 §4.2.1). That is what lets a JSON Schema `required` over `k` keys be tracked by a
horizontal state of size `O(k)` instead of the `2^k` an unordered reading needs (note 07 §1).

**Run certificates.** A `Run` labels every node with a state. `checkRun` verifies the labels
node-locally (one horizontal pass over the children's LABELS per node, never recursing into a
child's evaluation), which is the shape an AIR checks: one transition lookup per child edge, one
`hfinal` per node. `checkRun_sound`: an accepted run's root label is `eval`'s answer.
`checkRun_annotate`: the honest run (`annotate`) is always accepted.

**Counts** (`Counts`, `counts`): nodes, child edges (= horizontal transitions = transition
lookups), scalar leaves, string-leaf bytes (the byte DFA's lookups when the leaf automaton is a
byte table), and frames hashed with their Keccak-f count for the executable's SHAKE256 node hash.
-/
import Dregg2.Tree.Merkle

namespace Dregg2.Tree

/-- Container kind. -/
inductive Kind where
  | arr
  | obj
  deriving Repr, DecidableEq

/-- A deterministic bottom-up hedge automaton. `hstep h k q` reads one child (its key `k` for an
object, `none` for an array) whose state is `q`. -/
structure TreeAut (Q H : Type) where
  leaf : JVal → Option Q
  hstart : Kind → H
  hstep : H → Option (List UInt8) → Q → Option H
  hfinal : Kind → H → Option Q

namespace TreeAut

variable {Q H : Type} (A : TreeAut Q H)

mutual
/-- The automaton's state at a node (`none`: rejected). -/
def eval : JVal → Option Q
  | .arr xs => (evalArr xs (A.hstart .arr)).bind (A.hfinal .arr)
  | .obj kvs => (evalObj kvs (A.hstart .obj)).bind (A.hfinal .obj)
  | v => A.leaf v
def evalArr : List JVal → H → Option H
  | [], h => some h
  | x :: xs, h => match eval x with
    | none => none
    | some q => match A.hstep h none q with
      | none => none
      | some h' => evalArr xs h'
def evalObj : List (List UInt8 × JVal) → H → Option H
  | [], h => some h
  | (k, x) :: xs, h => match eval x with
    | none => none
    | some q => match A.hstep h (some k) q with
      | none => none
      | some h' => evalObj xs h'
end

/-- Acceptance at the root under a root predicate. -/
def Accepts (acc : Q → Bool) (t : JVal) : Prop := ∃ q, A.eval t = some q ∧ acc q = true

end TreeAut

/-! ## Run certificates -/

/-- A state-labelled tree, shaped like the value it labels. -/
inductive Run (Q : Type) where
  | leaf (q : Q)
  | node (q : Q) (kids : List (Run Q))
  deriving Repr

namespace Run
def label {Q : Type} : Run Q → Q
  | .leaf q => q
  | .node q _ => q
end Run

namespace TreeAut

variable {Q H : Type} [DecidableEq Q] (A : TreeAut Q H)

/-- One horizontal pass over the children's labels (no recursion into children). -/
def hrunArr : List (Run Q) → H → Option H
  | [], h => some h
  | r :: rs, h => match A.hstep h none r.label with
    | none => none
    | some h' => hrunArr rs h'

def hrunObj : List (List UInt8) → List (Run Q) → H → Option H
  | [], [], h => some h
  | k :: ks, r :: rs, h => match A.hstep h (some k) r.label with
    | none => none
    | some h' => hrunObj ks rs h'
  | _, _, _ => none

mutual
/-- ⚑ **The run checker.** Every node's label must be its local transition from its children's
labels; children are checked the same way. -/
def checkRun : JVal → Run Q → Bool
  | .arr xs, .node q rs =>
    xs.length == rs.length && (hrunArr A rs (A.hstart .arr)).bind (A.hfinal .arr) == some q &&
      checkRuns xs rs
  | .obj kvs, .node q rs =>
    kvs.length == rs.length &&
      (hrunObj A (kvs.map (·.1)) rs (A.hstart .obj)).bind (A.hfinal .obj) == some q &&
      checkRunsKV kvs rs
  | .arr _, .leaf _ => false
  | .obj _, .leaf _ => false
  | v, .leaf q => A.leaf v == some q
  | _, .node _ _ => false
def checkRuns : List JVal → List (Run Q) → Bool
  | [], [] => true
  | x :: xs, r :: rs => checkRun x r && checkRuns xs rs
  | _, _ => false
def checkRunsKV : List (List UInt8 × JVal) → List (Run Q) → Bool
  | [], [] => true
  | (_, x) :: xs, r :: rs => checkRun x r && checkRunsKV xs rs
  | _, _ => false
end

omit [DecidableEq Q] in
theorem hrunArr_eq : ∀ (xs : List JVal) (rs : List (Run Q)) (h : H),
    (∀ (i : Nat) (x : JVal) (r : Run Q), xs[i]? = some x → rs[i]? = some r → A.eval x = some r.label) →
    xs.length = rs.length → A.evalArr xs h = hrunArr A rs h
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl
  | x :: xs, r :: rs, h, hp, hl => by
    have e := hp 0 x r rfl rfl
    simp only [TreeAut.evalArr, hrunArr, e]
    split
    · rfl
    · exact hrunArr_eq xs rs _ (fun i x' r' h1 h2 => hp (i + 1) x' r' h1 h2) (by simpa using hl)

omit [DecidableEq Q] in
theorem hrunObj_eq : ∀ (xs : List (List UInt8 × JVal)) (rs : List (Run Q)) (h : H),
    (∀ (i : Nat) (x : List UInt8 × JVal) (r : Run Q), xs[i]? = some x → rs[i]? = some r →
      A.eval x.2 = some r.label) →
    xs.length = rs.length → A.evalObj xs h = hrunObj A (xs.map (·.1)) rs h
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl
  | (k, x) :: xs, r :: rs, h, hp, hl => by
    have e := hp 0 (k, x) r rfl rfl
    simp only [TreeAut.evalObj, List.map_cons, hrunObj, e]
    split
    · rfl
    · exact hrunObj_eq xs rs _ (fun i x' r' h1 h2 => hp (i + 1) x' r' h1 h2) (by simpa using hl)

mutual
/-- ⚑ **`checkRun_sound`** — an accepted run's root label is the automaton's state. -/
theorem checkRun_sound : ∀ (t : JVal) (r : Run Q), checkRun A t r = true → A.eval t = some r.label
  | .arr xs, .node q rs, h => by
    simp only [checkRun, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hl, hq⟩, hk⟩ := h
    simp only [TreeAut.eval, Run.label]
    rw [hrunArr_eq A xs rs _ (checkRuns_sound xs rs hk) hl, hq]
  | .obj kvs, .node q rs, h => by
    simp only [checkRun, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hl, hq⟩, hk⟩ := h
    simp only [TreeAut.eval, Run.label]
    rw [hrunObj_eq A kvs rs _ (checkRunsKV_sound kvs rs hk) hl, hq]
  | .arr _, .leaf _, h => by simp [checkRun] at h
  | .obj _, .leaf _, h => by simp [checkRun] at h
  | .null, .leaf q, h | .bool _, .leaf q, h | .int _, .leaf q, h | .dec _ _, .leaf q, h
  | .str _, .leaf q, h => by
    simp only [checkRun, beq_iff_eq] at h
    simp [TreeAut.eval, Run.label, h]
  | .null, .node _ _, h | .bool _, .node _ _, h | .int _, .node _ _, h | .dec _ _, .node _ _, h
  | .str _, .node _ _, h => by simp [checkRun] at h
theorem checkRuns_sound : ∀ (xs : List JVal) (rs : List (Run Q)), checkRuns A xs rs = true →
    ∀ (i : Nat) (x : JVal) (r : Run Q), xs[i]? = some x → rs[i]? = some r → A.eval x = some r.label
  | [], [], _, i, _, _, h1, _ => by simp at h1
  | x :: xs, r :: rs, h, 0, x', r', h1, h2 => by
    simp only [checkRuns, Bool.and_eq_true] at h
    simp at h1 h2; subst h1; subst h2
    exact checkRun_sound x r h.1
  | x :: xs, r :: rs, h, i + 1, x', r', h1, h2 => by
    simp only [checkRuns, Bool.and_eq_true] at h
    simp at h1 h2
    exact checkRuns_sound xs rs h.2 i x' r' h1 h2
  | [], _ :: _, h, _, _, _, _, _ => by simp [checkRuns] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [checkRuns] at h
theorem checkRunsKV_sound : ∀ (xs : List (List UInt8 × JVal)) (rs : List (Run Q)),
    checkRunsKV A xs rs = true → ∀ (i : Nat) (x : List UInt8 × JVal) (r : Run Q),
      xs[i]? = some x → rs[i]? = some r → A.eval x.2 = some r.label
  | [], [], _, i, _, _, h1, _ => by simp at h1
  | (k, x) :: xs, r :: rs, h, 0, x', r', h1, h2 => by
    simp only [checkRunsKV, Bool.and_eq_true] at h
    simp at h1 h2; subst h1; subst h2
    exact checkRun_sound x r h.1
  | (k, x) :: xs, r :: rs, h, i + 1, x', r', h1, h2 => by
    simp only [checkRunsKV, Bool.and_eq_true] at h
    simp at h1 h2
    exact checkRunsKV_sound xs rs h.2 i x' r' h1 h2
  | [], _ :: _, h, _, _, _, _, _ => by simp [checkRunsKV] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [checkRunsKV] at h
end

end TreeAut

/-! ## The honest run -/

namespace TreeAut

variable {Q H : Type} (A : TreeAut Q H) (dflt : Q)

mutual
/-- Label every node with its state (`dflt` where the automaton rejects; such runs are refused). -/
def annotate : JVal → Run Q
  | .arr xs => .node ((A.eval (.arr xs)).getD dflt) (annotateList xs)
  | .obj kvs => .node ((A.eval (.obj kvs)).getD dflt) (annotateKVs kvs)
  | v => .leaf ((A.eval v).getD dflt)
def annotateList : List JVal → List (Run Q)
  | [] => []
  | x :: xs => annotate x :: annotateList xs
def annotateKVs : List (List UInt8 × JVal) → List (Run Q)
  | [] => []
  | (_, x) :: xs => annotate x :: annotateKVs xs
end

end TreeAut

/-! ## Counts per node -/

/-- Per-tree operation counts (substrate-neutral; `SUBSTRATE-DECISION.md` §4). -/
structure Counts where
  nodes : Nat
  edges : Nat
  leaves : Nat
  strBytes : Nat
  frameBytes : Nat
  keccakF : Nat
  deriving Repr, DecidableEq

def Counts.add (a b : Counts) : Counts :=
  ⟨a.nodes + b.nodes, a.edges + b.edges, a.leaves + b.leaves, a.strBytes + b.strBytes,
    a.frameBytes + b.frameBytes, a.keccakF + b.keccakF⟩

/-- Keccak-f permutations for one SHAKE256 call over `n` input bytes (rate 136, `⌊n/136⌋+1`,
FIPS 202 padding included, one 32-byte squeeze). -/
def keccakFOf (n : Nat) : Nat := n / 136 + 1

/-- The node-hash prefix `"dregg.tree.node.v1" ‖ 0x00` is 19 bytes. -/
def nodePrefixLen : Nat := 19

section
variable (H : List UInt8 → Digest)

/-- The counts of one node's own work (its frame, its edges, its leaf bytes). -/
def nodeCounts (t : JVal) : Counts :=
  let fb := (frameOf H t).bytes.length
  let edges := match t with
    | .arr xs => xs.length
    | .obj kvs => kvs.length
    | _ => 0
  let leaf := if t.isScalar then 1 else 0
  let sb := match t with
    | .str s => s.length
    | _ => 0
  ⟨1, edges, leaf, sb, fb, keccakFOf (nodePrefixLen + fb)⟩

mutual
def counts : JVal → Counts
  | .arr xs => (nodeCounts H (.arr xs)).add (countsList xs)
  | .obj kvs => (nodeCounts H (.obj kvs)).add (countsKVs kvs)
  | v => nodeCounts H v
def countsList : List JVal → Counts
  | [] => ⟨0, 0, 0, 0, 0, 0⟩
  | x :: xs => (counts x).add (countsList xs)
def countsKVs : List (List UInt8 × JVal) → Counts
  | [] => ⟨0, 0, 0, 0, 0, 0⟩
  | (_, x) :: xs => (counts x).add (countsKVs xs)
end

end

/-- info: 'Dregg2.Tree.TreeAut.checkRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TreeAut.checkRun_sound

end Dregg2.Tree
