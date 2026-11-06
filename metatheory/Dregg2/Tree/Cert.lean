/-
# Dregg2.Tree.Cert: content-bound tree certificates (statement of data, checker, soundness)

Three statements, each data only, each checked by a total executable checker, each with a
soundness theorem in the shape of minidregg `Tower256ContentCert.named_or_collision`: for NAMED
content whose commitments are the statement's, an accepted receipt decides the claim about THAT
content, or the hash collides at a pair the theorem computes from the two (never an existential
over the hash).

| statement | commits | receipt discloses | theorem |
|---|---|---|---|
| `SchemaStmt` | tree root, schema digest | the record, the schema, a run | `schema_sound` |
| `FieldStmt` | tree root, path, table digest | one path opening, the table | `path_pattern_sound` |
| `CorpusStmt` | MMR root of record roots, `n`, a query, `count` | per record: its root and one or more path openings | `corpus_count_sound` here, `corpus_absence` (with MMR binding) in `Tree/Spec.lean` |

A schema and a byte table are themselves JSON values (`Schema.ofJVal`, `tableOfJVal`); they are
committed by a flat digest `F (encode v)` (one hash over the canonical CBOR), bound by
`canon_injective` (`flat_binds`). Records are committed by the Merkle root (`Merkle.digest`) so
that single paths open.

A `FieldStmt`'s verdict is one of four: the path is absent, the value there is not a string, or it
is a string the table accepts / rejects. A corpus query is a conjunction of `(path, table)`; a
record MATCHES when, for every conjunct, the value at the path is a string the table accepts. A
non-matching record is evidenced by ONE failing conjunct's opening (the record's `name` is not
`Bash`), so its other fields are never disclosed.
-/
import Dregg2.Tree.Schema

namespace Dregg2.Tree

open Cbor

/-! ## Flat digests (schemas, tables) -/

/-- One hash over the canonical bytes. -/
def flatDigest (F : List UInt8 → Digest) (v : JVal) : Digest := F (encode v)

/-- ⚑ A flat digest names one admitted value, or `F` collides at the two encodings. -/
theorem flat_binds {F : List UInt8 → Digest} {a b : JVal} (ha : Admitted a) (hb : Admitted b)
    (h : flatDigest F a = flatDigest F b) : a = b ∨ Coll F (encode a, encode b) := by
  by_cases e : encode a = encode b
  · exact Or.inl (canon_injective ha hb e)
  · exact Or.inr ⟨e, h⟩

/-! ## Reading schemas and tables from JSON values -/

private def key (s : String) : List UInt8 := s.toUTF8.toList

def asNat : JVal → Option Nat
  | .int n => if 0 ≤ n then some n.toNat else none
  | _ => none

def asInt : JVal → Option Int
  | .int n => some n
  | _ => none

def asStr : JVal → Option (List UInt8)
  | .str s => some s
  | _ => none

def asList {α : Type} (f : JVal → Option α) : JVal → Option (List α)
  | .arr xs => xs.mapM f
  | _ => none

def tyOfName (s : List UInt8) : Option Ty :=
  if s = key "null" then some .null
  else if s = key "boolean" then some .bool
  else if s = key "integer" then some .int
  else if s = key "number" then some .num
  else if s = key "string" then some .str
  else if s = key "array" then some .arr
  else if s = key "object" then some .obj
  else none

def asTypes : JVal → Option (List Ty)
  | .str s => (tyOfName s).map ([·])
  | .arr xs => xs.mapM fun x => (asStr x).bind tyOfName
  | _ => none

/-- The keywords of the regular core. Any other key is refused, so a schema that says
`uniqueItems` is never silently read as one that does not. -/
def knownKeys : List (List UInt8) :=
  ["type", "enum", "pattern", "minimum", "maximum", "properties", "required",
   "additionalProperties", "items", "minItems", "maxItems", "allOf", "anyOf"].map key

def defOfJVal : JVal → Option Def
  | .obj kvs => do
    if !(kvs.all fun e => knownKeys.contains e.1) then none
    let get (k : String) : Option JVal := findKey (key k) kvs
    let opt {α : Type} (k : String) (f : JVal → Option α) : Option (Option α) :=
      match get k with
      | none => some none
      | some v => (f v).map some
    -- an explicit empty `type`, `enum`, `allOf` or `anyOf` is refused, never read as "absent"
    -- (codex round 1, finding 2)
    let nonEmpty {α : Type} (f : JVal → Option (List α)) (v : JVal) : Option (List α) :=
      match f v with
      | some (x :: xs) => some (x :: xs)
      | _ => none
    let types ← opt "type" (nonEmpty asTypes)
    let enumStr ← opt "enum" (nonEmpty (asList asStr))
    let pattern ← opt "pattern" asNat
    let minimum ← opt "minimum" asInt
    let maximum ← opt "maximum" asInt
    let props ← opt "properties" fun
      | .obj ps => ps.mapM fun e => (asNat e.2).map (e.1, ·)
      | _ => none
    let required ← opt "required" (asList asStr)
    let additional ← opt "additionalProperties" fun
      | .bool true => some Addl.any
      | .bool false => some Addl.forbid
      | v => (asNat v).map Addl.sch
    let items ← opt "items" asNat
    let minItems ← opt "minItems" asNat
    let maxItems ← opt "maxItems" asNat
    let allOf ← opt "allOf" (nonEmpty (asList asNat))
    let anyOf ← opt "anyOf" (nonEmpty (asList asNat))
    pure { types := types.getD [], enumStr, pattern, minimum, maximum, props := props.getD [],
           required := required.getD [], additional := additional.getD .any, items,
           minItems := minItems.getD 0, maxItems, allOf := allOf.getD [], anyOf := anyOf.getD [] }
  | _ => none

/-- A byte table in the `dfa` crate's shape: `num_states`, `transitions`, `start`, `accepting`. -/
def tableOfJVal : JVal → Option FlatTable
  | .obj kvs => do
    if !(kvs.all fun e => (["accepting", "num_states", "start", "transitions"].map key).contains e.1) then none
    let n ← (findKey (key "num_states") kvs).bind asNat
    let tr ← (findKey (key "transitions") kvs).bind (asList asNat)
    let st ← (findKey (key "start") kvs).bind asNat
    let acc ← (findKey (key "accepting") kvs).bind (asList asNat)
    let t : FlatTable := { numStates := n, transitions := tr.toArray, start := st, accepting := acc }
    if t.wellFormed then some t else none
  | _ => none

/-- `{"defs": [...], "root": n, "tables": [...]}`. -/
def schemaOfJVal : JVal → Option Schema
  | .obj kvs => do
    if !(kvs.all fun e => (["defs", "root", "tables"].map key).contains e.1) then none
    let defs ← (findKey (key "defs") kvs).bind (asList defOfJVal)
    let root ← (findKey (key "root") kvs).bind asNat
    let tables ← match findKey (key "tables") kvs with
      | none => some []
      | some v => asList tableOfJVal v
    let S : Schema := { defs, tables, root }
    if S.ok then some S else none
  | _ => none

/-! ## 1. Schema certificates -/

section
variable (H F : List UInt8 → Digest)

/-- **The schema statement** (data only). -/
structure SchemaStmt where
  treeRoot : Digest
  schemaDigest : Digest
  verdict : Bool
  deriving Repr, DecidableEq

structure SchemaReceipt where
  tree : JVal
  schema : JVal
  run : Run (List Bool)
  deriving Repr

/-- The relation, decided. -/
def schemaCheck (st : SchemaStmt) (r : SchemaReceipt) : Bool :=
  decide (TreeAdm r.tree) && decide (WF r.tree) && digest H r.tree == st.treeRoot &&
  decide (Admitted r.schema) && flatDigest F r.schema == st.schemaDigest &&
  match schemaOfJVal r.schema with
  | none => false
  | some S => TreeAut.checkRun (compile S) r.tree r.run && getBit r.run.label S.root == st.verdict

end

section
variable {H F : List UInt8 → Digest}

/-- ⚑ **`schema_sound`** — for a named record and a named schema committed by the statement, an
accepted receipt IS them and the schema's verdict on the record is the claimed one, or the tree
hash collides at the pair `rootFind` names, or the flat hash collides at the two encodings. -/
theorem schema_sound (hH : HashFits H) (st : SchemaStmt) (r : SchemaReceipt)
    (acc : schemaCheck H F st r = true)
    (t s : JVal) (ht : TreeAdm t) (hs : Admitted s)
    (htr : digest H t = st.treeRoot) (hsd : flatDigest F s = st.schemaDigest) :
    (r.tree = t ∧ r.schema = s ∧ ∃ S, schemaOfJVal s = some S ∧ valid S t S.root = st.verdict) ∨
      Coll H (rootFind H r.tree t) ∨ Coll F (encode r.schema, encode s) := by
  unfold schemaCheck at acc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at acc
  obtain ⟨⟨⟨⟨⟨hta, _⟩, hd⟩, hsa⟩, hfd⟩, hm⟩ := acc
  rcases rootFind_sound hH r.tree t hta ht (by rw [hd, htr]) with e1 | e1
  · rcases flat_binds hsa hs (by rw [hfd, hsd]) with e2 | e2
    · left
      refine ⟨e1, e2, ?_⟩
      split at hm
      · cases hm
      · rename_i S hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        refine ⟨S, by rw [← e2]; exact hS, ?_⟩
        have hr := TreeAut.checkRun_sound (compile S) r.tree r.run hm.1
        rw [compile_correct] at hr
        have hb := congrArg (fun l => getBit l S.root) (Option.some.inj hr)
        simp only at hb
        rw [← e1, ← hm.2, ← getBit_bitsOf S r.tree S.root, hb]
    · exact Or.inr (Or.inr e2)
  · exact Or.inr (Or.inl e1)

end

/-! ## 2. Field (path ∘ pattern) certificates -/

/-- What the value at a path is, relative to a byte table. -/
inductive FieldVerdict where
  | absent
  | nonString
  | accept
  | reject
  deriving Repr, DecidableEq

def classify (T : FlatTable) : Option JVal → FieldVerdict
  | none => .absent
  | some (.str s) => if tableAccepts T s then .accept else .reject
  | some _ => .nonString

section
variable (H F : List UInt8 → Digest)

structure FieldStmt where
  treeRoot : Digest
  path : Path
  tableDigest : Digest
  verdict : FieldVerdict
  deriving Repr, DecidableEq

structure FieldReceipt where
  opening : Opening
  table : JVal
  deriving Repr

def fieldCheck (st : FieldStmt) (r : FieldReceipt) : Bool :=
  decide (Admitted r.table) && flatDigest F r.table == st.tableDigest &&
  match tableOfJVal r.table, walk H st.treeRoot st.path r.opening with
  | some T, some o => classify T o == st.verdict
  | _, _ => false

end

section
variable {H F : List UInt8 → Digest}

/-- ⚑ **`path_pattern_sound`** — the claimed verdict is the named table's verdict on the named
record's value at the path, or a collision at a computed pair. The string check is the house byte
table (`TableRunSpec` makes it `Dfa.lean`'s `DfaAccepts`; `Spec.lean` composes it with Layer B′). -/
theorem path_pattern_sound (hH : HashFits H) (st : FieldStmt) (r : FieldReceipt)
    (acc : fieldCheck H F st r = true)
    (t tab : JVal) (ht : TreeAdm t) (htab : Admitted tab)
    (htr : digest H t = st.treeRoot) (hfd : flatDigest F tab = st.tableDigest) :
    (r.table = tab ∧ ∃ T, tableOfJVal tab = some T ∧ classify T (lookup t st.path) = st.verdict) ∨
      Coll H (walkFind H t st.path r.opening) ∨ Coll F (encode r.table, encode tab) := by
  unfold fieldCheck at acc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at acc
  obtain ⟨⟨ha, hd⟩, hm⟩ := acc
  rcases flat_binds ha htab (by rw [hd, hfd]) with e2 | e2
  · split at hm
    · rename_i T o hT hw
      simp only [beq_iff_eq] at hm
      rw [← htr] at hw
      rcases walk_sound hH st.path r.opening t o ht hw with e1 | e1
      · left
        exact ⟨e2, T, by rw [← e2]; exact hT, by rw [← e1]; exact hm⟩
      · exact Or.inr (Or.inl e1)
    · cases hm
  · exact Or.inr (Or.inr e2)

end

/-! ## 3. Corpus certificates -/

/-! ### The MMR (a core-only copy of `Lightclient.MMR`; `Spec.mrootC_eq` proves it IS `MMR.mroot`) -/

inductive PTreeC where
  | leaf (v : Int)
  | node (l r : PTreeC)

def PTreeC.height : PTreeC → Nat
  | .leaf _ => 0
  | .node l _ => l.height + 1

def PTreeC.hashOf (hash : List Int → Int) : PTreeC → Int
  | .leaf v => hash [v]
  | .node l r => hash [l.hashOf hash, r.hashOf hash]

def pushC : List PTreeC → PTreeC → List PTreeC
  | [], t => [t]
  | s :: rest, t => if t.height = s.height then pushC rest (.node s t) else t :: s :: rest

def peaksOfC (L : List Int) : List PTreeC := L.foldl (fun f v => pushC f (.leaf v)) []

def bagC (hash : List Int → Int) : List PTreeC → Int
  | [] => hash []
  | t :: rest => hash [t.hashOf hash, bagC hash rest]

def mrootC (hash : List Int → Int) (L : List Int) : Int := bagC hash (peaksOfC L)

/-- `mapM` for `Option`, with the recursion spelled out (what the proofs induct on). -/
def optMap {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => match f x, optMap f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-! ### The statement -/

/-- One conjunct of a query: the value at `path` is a string `table` accepts. -/
structure Conjunct where
  path : Path
  tableDigest : Digest
  deriving Repr, DecidableEq

structure CorpusStmt where
  mmrRoot : Int
  n : Nat
  query : List Conjunct
  count : Nat
  deriving Repr, DecidableEq

/-- Per record: its root and either a refutation (one conjunct's opening, showing it fails) or a
full match (one opening per conjunct, in order, all accepting). -/
inductive RecEvidence where
  | refute (root : Digest) (j : Nat) (op : Opening)
  | full (root : Digest) (ops : List Opening)
  deriving Repr

def RecEvidence.root : RecEvidence → Digest
  | .refute r _ _ => r
  | .full r _ => r

structure CorpusReceipt where
  tables : List JVal
  records : List RecEvidence
  deriving Repr

/-- Does a record match the query (semantics)? -/
def matchesQ (Ts : List FlatTable) (q : List Conjunct) (t : JVal) : Bool :=
  (q.zip Ts).all fun c => classify c.2 (lookup t c.1.path) == .accept

section
variable (H F : List UInt8 → Digest)

/-- One record's evidence, judged: `some true` (matches), `some false` (refuted), `none`
(malformed: an opening that does not verify, a "refutation" that accepts, a short match). -/
def judge (q : List Conjunct) (Ts : List FlatTable) : RecEvidence → Option Bool
  | .refute root j op =>
    match q[j]?, Ts[j]? with
    | some c, some T =>
      match walk H root c.path op with
      | some o => if classify T o != .accept then some false else none
      | none => none
    | _, _ => none
  | .full root ops =>
    if q.length = Ts.length ∧ ops.length = q.length ∧
      ((q.zip Ts).zip ops).all (fun x => match walk H root x.1.1.path x.2 with
        | some o => classify x.1.2 o == .accept
        | none => false)
    then some true else none

/-- Digests as MMR leaves: big-endian naturals. -/
def leafOf (d : Digest) : Int := (ofBE d : Int)

/-- ⚑ **The corpus checker.** -/
def corpusCheck (hash : List Int → Int) (st : CorpusStmt) (r : CorpusReceipt) : Bool :=
  r.tables.length == st.query.length &&
  (r.tables.zip st.query).all (fun p => decide (Admitted p.1) && flatDigest F p.1 == p.2.tableDigest) &&
  match optMap tableOfJVal r.tables with
  | none => false
  | some Ts =>
    r.records.length == st.n && r.records.all (fun ev => ev.root.length == 32) &&
    mrootC hash (r.records.map (leafOf ·.root)) == st.mmrRoot &&
    match optMap (judge H st.query Ts) r.records with
    | none => false
    | some vs => (vs.filter id).length == st.count

end

/-! ### Soundness relative to the receipt's own leaves

`corpus_count_sound`: an accepted receipt's leaves have the statement's MMR root and length, and
for EVERY list of named records whose digests are those leaves (pointwise), the count of records
matching the query is the claimed count, unless a named collision occurs (an opening at some record,
or a table encoding). `Spec.corpus_absence` composes this with `MMR.mroot_binds_or_collides`, which
turns "named records under the statement's MMR root" into "digests equal to the receipt's leaves"
or an MMR collision. -/

section
variable {H F : List UInt8 → Digest}

/-- The collision a record's evidence can expose, at computed pairs. -/
def EvColl (H : List UInt8 → Digest) (q : List Conjunct) (t : JVal) : RecEvidence → Prop
  | .refute _ j op => ∃ c : Conjunct, q[j]? = some c ∧ Coll H (walkFind H t c.path op)
  | .full _ ops => ∃ (i : Nat) (c : Conjunct) (op : Opening), q[i]? = some c ∧ ops[i]? = some op ∧
      Coll H (walkFind H t c.path op)

theorem judge_sound (hH : HashFits H) {q : List Conjunct} {Ts : List FlatTable} {ev : RecEvidence}
    {b : Bool} (hj : judge H q Ts ev = some b) (t : JVal) (ht : TreeAdm t)
    (hroot : digest H t = ev.root) :
    b = matchesQ Ts q t ∨ EvColl H q t ev := by
  cases ev with
  | refute root j op =>
    simp only [RecEvidence.root] at hroot
    simp only [judge] at hj
    split at hj
    · rename_i c T hc hT
      split at hj
      · rename_i o hw
        rw [← hroot] at hw
        rcases walk_sound hH c.path op t o ht hw with e | e
        · left
          split at hj
          · rename_i hna
            cases hj
            symm
            unfold matchesQ
            rw [List.all_eq_false]
            refine ⟨(c, T), ?_, ?_⟩
            · rw [List.mem_iff_getElem?]
              exact ⟨j, by simp [List.getElem?_zip_eq_some, hc, hT]⟩
            · rw [← e]; simpa using hna
          · cases hj
        · exact Or.inr ⟨c, hc, e⟩
      · cases hj
    · cases hj
  | full root ops =>
    simp only [RecEvidence.root] at hroot
    simp only [judge] at hj
    split at hj
    · rename_i hc
      obtain ⟨hl1, hl2, hall⟩ := hc
      cases hj
      by_cases hcoll : EvColl H q t (.full root ops)
      · exact Or.inr hcoll
      · left
        symm
        unfold matchesQ
        rw [List.all_eq_true]
        intro p hp
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
        rw [List.getElem?_zip_eq_some] at hi
        obtain ⟨hc, hT⟩ := hi
        have hlt : i < ops.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1; omega
        have hop : ops[i]? = some ops[i] := List.getElem?_eq_getElem hlt
        have hmem : ((p.1, p.2), ops[i]) ∈ (q.zip Ts).zip ops := by
          rw [List.mem_iff_getElem?]
          exact ⟨i, by simp [List.getElem?_zip_eq_some, hc, hT, hop]⟩
        have := List.all_eq_true.mp hall _ hmem
        simp only at this
        split at this
        · rename_i o hw
          rw [← hroot] at hw
          rcases walk_sound hH p.1.path ops[i] t o ht hw with e | e
          · rw [← e]; simpa using this
          · exact absurd ⟨i, p.1, ops[i], hc, hop, e⟩ hcoll
        · cases this
    · cases hj

theorem count_eq (hH : HashFits H) (q : List Conjunct) (Ts : List FlatTable) :
    ∀ (L : List JVal) (recs : List RecEvidence) (vs : List Bool),
      optMap (judge H q Ts) recs = some vs → L.map (digest H) = recs.map (·.root) →
      (∀ t ∈ L, TreeAdm t) →
      (vs.filter id).length = (L.filter (matchesQ Ts q)).length ∨
        ∃ (i : Nat) (t : JVal) (ev : RecEvidence), L[i]? = some t ∧ recs[i]? = some ev ∧ EvColl H q t ev
  | [], [], vs, h, _, _ => by simp [optMap] at h; subst h; simp
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | t :: L, ev :: recs, vs, h, hr, ha => by
    simp only [optMap] at h
    split at h
    · rename_i b bs hb hbs
      cases h
      simp only [List.map_cons, List.cons.injEq] at hr
      rcases judge_sound hH hb t (ha t (by simp)) hr.1 with e | e
      · rcases count_eq hH q Ts L recs bs hbs hr.2 (fun x hx => ha x (by simp [hx])) with e2 | e2
        · left
          subst e
          cases hm : matchesQ Ts q t <;> simp [List.filter_cons, hm, e2]
        · right
          obtain ⟨i, t', ev', h1, h2, h3⟩ := e2
          exact ⟨i + 1, t', ev', by simpa using h1, by simpa using h2, h3⟩
      · exact Or.inr ⟨0, t, ev, rfl, rfl, e⟩
    · cases h

theorem tables_eq {F : List UInt8 → Digest} :
    ∀ (rt tabs : List JVal) (q : List Conjunct),
      rt.length = q.length →
      (rt.zip q).all (fun p => decide (Admitted p.1) && flatDigest F p.1 == p.2.tableDigest) = true →
      tabs.map (flatDigest F) = q.map (·.tableDigest) → (∀ x ∈ tabs, Admitted x) →
      rt = tabs ∨ ∃ (i : Nat) (a b : JVal), rt[i]? = some a ∧ tabs[i]? = some b ∧
        Coll F (encode a, encode b)
  | [], [], _, _, _, _, _ => Or.inl rfl
  | [], _ :: _, q, hl, _, hd, _ => by
    have := congrArg List.length hd; simp at this hl; omega
  | _ :: _, [], q, hl, _, hd, _ => by
    have := congrArg List.length hd; simp at this hl; omega
  | a :: rt, b :: tabs, [], hl, _, _, _ => by simp at hl
  | a :: rt, b :: tabs, c :: q, hl, hall, hd, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hall
    simp only [List.map_cons, List.cons.injEq] at hd
    rcases flat_binds hall.1.1 (ha b (by simp)) (by rw [hall.1.2, hd.1]) with e | e
    · rcases tables_eq rt tabs q (by simpa using hl) hall.2 hd.2 (fun x hx => ha x (by simp [hx]))
        with e2 | e2
      · exact Or.inl (by rw [e, e2])
      · right
        obtain ⟨i, a', b', h1, h2, h3⟩ := e2
        exact ⟨i + 1, a', b', by simpa using h1, by simpa using h2, h3⟩
    · exact Or.inr ⟨0, a, b, rfl, rfl, e⟩

/-- ⚑ **`corpus_count_sound`** — for named records whose digests are the accepted receipt's
leaves and named tables committed by the statement, the number of records matching the query is
the claimed count, or a collision occurs at a computed pair (an opening of some record, or a table
encoding). -/
theorem corpus_count_sound (hH : HashFits H) (hash : List Int → Int) (st : CorpusStmt)
    (r : CorpusReceipt) (acc : corpusCheck H F hash st r = true)
    (L : List JVal) (hL : ∀ t ∈ L, TreeAdm t)
    (hroots : L.map (digest H) = r.records.map (·.root))
    (tabs : List JVal) (htabs : ∀ x ∈ tabs, Admitted x)
    (htd : tabs.map (flatDigest F) = st.query.map (·.tableDigest)) :
    (∃ Ts, optMap tableOfJVal tabs = some Ts ∧
        (L.filter (matchesQ Ts st.query)).length = st.count) ∨
      (∃ (i : Nat) (t : JVal) (ev : RecEvidence), L[i]? = some t ∧ r.records[i]? = some ev ∧
        EvColl H st.query t ev) ∨
      (∃ (i : Nat) (a b : JVal), r.tables[i]? = some a ∧ tabs[i]? = some b ∧
        Coll F (encode a, encode b)) := by
  unfold corpusCheck at acc
  simp only [Bool.and_eq_true, beq_iff_eq] at acc
  obtain ⟨⟨hl, hall⟩, hm⟩ := acc
  rcases tables_eq r.tables tabs st.query hl hall htd htabs with et | et
  · split at hm
    · cases hm
    · rename_i Ts hTs
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨⟨_, _⟩, _⟩, hm⟩ := hm
      split at hm
      · cases hm
      · rename_i vs hvs
        simp only [beq_iff_eq] at hm
        rcases count_eq hH st.query Ts L r.records vs hvs hroots hL with e | e
        · exact Or.inl ⟨Ts, by rw [← et]; exact hTs, by rw [← e, hm]⟩
        · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr et)

end

/-- info: 'Dregg2.Tree.schema_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms schema_sound

/-- info: 'Dregg2.Tree.path_pattern_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms path_pattern_sound

/-- info: 'Dregg2.Tree.corpus_count_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms corpus_count_sound

/-- info: 'Dregg2.Tree.judge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms judge_sound

end Dregg2.Tree
