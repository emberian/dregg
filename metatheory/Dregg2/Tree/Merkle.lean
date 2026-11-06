/-
# Dregg2.Tree.Merkle: the Merkleized tree commitment, single-path openings, and their soundness

A node's digest is `H` of its **frame**, a CBOR item (`Frame.item`) that is:

    leaf v      ↦ [0, toItem v]                       (the scalar's canonical item)
    arr xs      ↦ [1, [bstr (digest x) | x ∈ xs]]
    obj kvs     ↦ [2, {text k : bstr (digest v) | (k, v) ∈ kvs}]

The leading kind discriminator is load-bearing: without it, `[]` and `{}` would frame alike
whenever the object's entries are framed as an array of pairs (the falsifier `weak*` below).
Frames are injective on the admitted domain (`Frame.bytes_injective`, from `Cbor.enc_injective`),
so equal digests at unequal frames are a collision of `H` at a pair this module computes.

**Openings.** An `Opening` walks a `Path` from the root: at each level it discloses the node's
frame (all child digests, and an object's keys), the walk picks the child the path names, and at
the end it either discloses a whole subtree (`here v`) or shows the next step is not in the node
(`absentArr`/`absentObj`). `walk` recomputes every frame and digest top-down from the claimed root.
Sibling VALUES stay hidden (only their digests appear); sibling KEYS of the opened objects do not.

**Soundness, in the `ContentCert` shape.** `walk_sound`: if `walk` accepts against the digest of a
named, admitted tree `t`, its outcome IS `lookup t p`, or `H` collides at the pair
`walkFind H t p op` computes from `t` and the opening (never an existential over the hash).
`rootFind_sound` is the whole-tree case: two admitted trees under one digest are equal, or `H`
collides at the pair `rootFind` names.
-/
import Dregg2.Tree.Value
import Dregg2.Crypto.Keccak

namespace Dregg2.Tree

open Cbor

abbrev Digest := List UInt8

/-- A node's frame: what its digest hashes. -/
inductive Frame where
  | leaf (v : JVal)
  | arr (ds : List Digest)
  | obj (es : List (List UInt8 × Digest))
  deriving Repr, DecidableEq

namespace Frame

def item : Frame → Item
  | .leaf v => .arr [.uint 0, toItem v]
  | .arr ds => .arr [.uint 1, .arr (ds.map .bytes)]
  | .obj es => .arr [.uint 2, .map (es.map fun e => (.text e.1, .bytes e.2))]

def bytes (f : Frame) : List UInt8 := enc f.item

/-- Admitted frames (decidable): every head argument fits. -/
def Adm (f : Frame) : Prop := Cbor.Adm f.item

instance (f : Frame) : Decidable f.Adm := by unfold Frame.Adm; rw [← adm_iff]; infer_instance

theorem map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ l l' : List α, l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_inj hf l l' h.2]

theorem item_injective {f g : Frame} (h : f.item = g.item) : f = g := by
  cases f <;> cases g <;> simp only [item, Item.arr.injEq, Item.map.injEq, List.cons.injEq,
    Item.uint.injEq, and_true] at h <;> (try omega)
  · rw [toItem_injective h.2]
  · rename_i ds ds'
    have : ds = ds' := map_inj (fun a b h => by cases h; rfl) ds ds' h.2
    rw [this]
  · rename_i es es'
    have : es = es' := by
      refine map_inj ?_ es es' h.2
      intro a b hab
      simp only [Prod.mk.injEq, Item.text.injEq, Item.bytes.injEq] at hab
      exact Prod.ext hab.1 hab.2
    rw [this]

/-- ⚑ Frames are injective on the admitted domain. -/
theorem bytes_injective {f g : Frame} (hf : f.Adm) (hg : g.Adm) (h : f.bytes = g.bytes) : f = g :=
  item_injective (enc_injective hf hg h)

end Frame

section
variable (H : List UInt8 → Digest)

mutual
/-- The digest of a node. -/
def digest : JVal → Digest
  | .arr xs => H (Frame.arr (digests xs)).bytes
  | .obj kvs => H (Frame.obj (digestKVs kvs)).bytes
  | v => H (Frame.leaf v).bytes
def digests : List JVal → List Digest
  | [] => []
  | x :: xs => digest x :: digests xs
def digestKVs : List (List UInt8 × JVal) → List (List UInt8 × Digest)
  | [] => []
  | (k, v) :: kvs => (k, digest v) :: digestKVs kvs
end

/-- The frame of a node. -/
def frameOf : JVal → Frame
  | .arr xs => .arr (digests H xs)
  | .obj kvs => .obj (digestKVs H kvs)
  | v => .leaf v

theorem digest_eq_frame (v : JVal) : digest H v = H (frameOf H v).bytes := by
  cases v <;> simp [digest, frameOf]

theorem digests_length : ∀ xs : List JVal, (digests H xs).length = xs.length
  | [] => rfl
  | _ :: xs => by simp [digests, digests_length xs]

theorem digests_getElem? : ∀ (xs : List JVal) (i : Nat),
    (digests H xs)[i]? = xs[i]?.map (digest H)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => by simp [digests, digests_getElem? xs i]

end

/-- A collision of `H` at a named pair. -/
def Coll (H : List UInt8 → Digest) (w : List UInt8 × List UInt8) : Prop :=
  w.1 ≠ w.2 ∧ H w.1 = H w.2

instance (H : List UInt8 → Digest) (w : List UInt8 × List UInt8) : Decidable (Coll H w) := by
  unfold Coll; infer_instance

/-! ## Admissibility of a tree's frames -/

/-- Every frame of the tree is admitted, given that `H`'s outputs fit a 64-bit head. -/
def HashFits (H : List UInt8 → Digest) : Prop := ∀ x, (H x).length < 2 ^ 64

mutual
/-- The structural side condition the named tree carries: admitted scalars and container sizes
below `2^64`. (Every real JSON document satisfies it; `Admitted` implies it, `admitted_treeAdm`.) -/
def TreeAdm : JVal → Prop
  | .arr xs => xs.length < 2 ^ 64 ∧ TreeAdmList xs
  | .obj kvs => kvs.length < 2 ^ 64 ∧ TreeAdmKVs kvs
  | v => Admitted v
def TreeAdmList : List JVal → Prop
  | [] => True
  | x :: xs => TreeAdm x ∧ TreeAdmList xs
def TreeAdmKVs : List (List UInt8 × JVal) → Prop
  | [] => True
  | (k, v) :: kvs => k.length < 2 ^ 64 ∧ TreeAdm v ∧ TreeAdmKVs kvs
end

mutual
def treeAdm : JVal → Bool
  | .arr xs => xs.length < 2 ^ 64 && treeAdmList xs
  | .obj kvs => kvs.length < 2 ^ 64 && treeAdmKVs kvs
  | v => adm (toItem v)
def treeAdmList : List JVal → Bool
  | [] => true
  | x :: xs => treeAdm x && treeAdmList xs
def treeAdmKVs : List (List UInt8 × JVal) → Bool
  | [] => true
  | (k, v) :: kvs => k.length < 2 ^ 64 && treeAdm v && treeAdmKVs kvs
end

mutual
theorem treeAdm_iff : ∀ v : JVal, treeAdm v = true ↔ TreeAdm v
  | .arr xs => by simp [treeAdm, TreeAdm, treeAdmList_iff xs]
  | .obj kvs => by simp [treeAdm, TreeAdm, treeAdmKVs_iff kvs]
  | .null => by simp [treeAdm, TreeAdm, Admitted, adm_iff]
  | .bool _ => by simp [treeAdm, TreeAdm, Admitted, adm_iff]
  | .int _ => by simp [treeAdm, TreeAdm, Admitted, adm_iff]
  | .dec _ _ => by simp [treeAdm, TreeAdm, Admitted, adm_iff]
  | .str _ => by simp [treeAdm, TreeAdm, Admitted, adm_iff]
theorem treeAdmList_iff : ∀ xs : List JVal, treeAdmList xs = true ↔ TreeAdmList xs
  | [] => by simp [treeAdmList, TreeAdmList]
  | x :: xs => by simp [treeAdmList, TreeAdmList, treeAdm_iff x, treeAdmList_iff xs]
theorem treeAdmKVs_iff : ∀ kvs : List (List UInt8 × JVal), treeAdmKVs kvs = true ↔ TreeAdmKVs kvs
  | [] => by simp [treeAdmKVs, TreeAdmKVs]
  | (k, v) :: kvs => by simp [treeAdmKVs, TreeAdmKVs, treeAdm_iff v, treeAdmKVs_iff kvs, and_assoc]
end

instance (v : JVal) : Decidable (TreeAdm v) := decidable_of_iff _ (treeAdm_iff v)

section
variable {H : List UInt8 → Digest}

theorem admList_map_bytes (hH : HashFits H) :
    ∀ ds : List Digest, (∀ d ∈ ds, d.length < 2 ^ 64) → AdmList (ds.map Item.bytes)
  | [], _ => trivial
  | d :: ds, h => ⟨h d (by simp), admList_map_bytes hH ds (fun x hx => h x (by simp [hx]))⟩

theorem digests_mem_fits (hH : HashFits H) (xs : List JVal) :
    ∀ d ∈ digests H xs, d.length < 2 ^ 64 := by
  induction xs with
  | nil => simp [digests]
  | cons x xs ih =>
    intro d hd
    simp only [digests, List.mem_cons] at hd
    rcases hd with rfl | hd
    · cases x <;> simp only [digest] <;> exact hH _
    · exact ih d hd

theorem admPairs_map (hH : HashFits H) :
    ∀ kvs : List (List UInt8 × JVal), TreeAdmKVs kvs →
      AdmPairs ((digestKVs H kvs).map fun e => (Item.text e.1, Item.bytes e.2))
  | [], _ => trivial
  | (k, v) :: kvs, h => by
    refine ⟨h.1, ?_, admPairs_map hH kvs h.2.2⟩
    cases v <;> simp only [digest] <;> exact hH _

theorem digestKVs_length : ∀ kvs : List (List UInt8 × JVal), (digestKVs H kvs).length = kvs.length
  | [] => rfl
  | _ :: kvs => by simp [digestKVs, digestKVs_length kvs]

/-- The named tree's own frame is admitted. -/
theorem frameOf_adm (hH : HashFits H) : ∀ t : JVal, TreeAdm t → (frameOf H t).Adm
  | .arr xs, h => by
    simp only [Frame.Adm, frameOf, Frame.item, Cbor.Adm, AdmList, List.length_cons,
      List.length_nil, List.length_map, digests_length, and_true]
    exact ⟨by omega, by omega, h.1, admList_map_bytes hH _ (digests_mem_fits hH xs)⟩
  | .obj kvs, h => by
    simp only [Frame.Adm, frameOf, Frame.item, Cbor.Adm, AdmList, List.length_cons,
      List.length_nil, List.length_map, digestKVs_length, and_true]
    exact ⟨by omega, by omega, h.1, admPairs_map hH kvs h.2⟩
  | .null, h | .bool _, h | .int _, h | .dec _ _, h | .str _, h => by
    simp only [Frame.Adm, frameOf, Frame.item, Cbor.Adm, AdmList, List.length_cons,
      List.length_nil, and_true]
    exact ⟨by omega, by omega, h⟩

end

/-! ## Whole-tree binding: equal digests, equal trees, or a named collision -/

section
variable (H : List UInt8 → Digest)

mutual
/-- **The pair two trees under one digest collide at**: their two frames if those differ, else the
first differing child pair, recursively. -/
def rootFind (a b : JVal) : List UInt8 × List UInt8 :=
  if (frameOf H a).bytes = (frameOf H b).bytes then
    match a, b with
    | .arr xs, .arr ys => rootFindList xs ys
    | .obj xs, .obj ys => rootFindKVs xs ys
    | _, _ => ((frameOf H a).bytes, (frameOf H b).bytes)
  else ((frameOf H a).bytes, (frameOf H b).bytes)
def rootFindList : List JVal → List JVal → List UInt8 × List UInt8
  | x :: xs, y :: ys => if x = y then rootFindList xs ys else rootFind x y
  | _, _ => ([], [])
def rootFindKVs : List (List UInt8 × JVal) → List (List UInt8 × JVal) → List UInt8 × List UInt8
  | (_, x) :: xs, (_, y) :: ys => if x = y then rootFindKVs xs ys else rootFind x y
  | _, _ => ([], [])
end

end

section
variable {H : List UInt8 → Digest}

/-- Equal digests and unequal frames: the frames are the collision. -/
theorem coll_of_frames {a b : JVal} (hd : digest H a = digest H b)
    (hf : (frameOf H a).bytes ≠ (frameOf H b).bytes) :
    Coll H ((frameOf H a).bytes, (frameOf H b).bytes) :=
  ⟨hf, by rw [← digest_eq_frame H a, ← digest_eq_frame H b]; exact hd⟩

mutual
/-- ⚑ **`rootFind_sound`** — one digest, one tree, or `H` collides at the pair `rootFind` names. -/
theorem rootFind_sound (hH : HashFits H) (a b : JVal) (ha : TreeAdm a) (hb : TreeAdm b)
    (hd : digest H a = digest H b) : a = b ∨ Coll H (rootFind H a b) := by
  by_cases hf : (frameOf H a).bytes = (frameOf H b).bytes
  · have he := Frame.bytes_injective (frameOf_adm hH _ ha) (frameOf_adm hH _ hb) hf
    cases a <;> cases b <;> simp only [frameOf, Frame.leaf.injEq, Frame.arr.injEq, Frame.obj.injEq,
      reduceCtorEq] at he
    all_goals first
      | (left; rfl)
      | (left; rw [he])
      | (rename_i xs ys
         unfold rootFind; rw [if_pos hf]
         rcases rootFindList_sound hH xs ys ha.2 hb.2 he with h | h
         · exact Or.inl (by rw [h])
         · exact Or.inr h)
      | (rename_i xs ys
         unfold rootFind; rw [if_pos hf]
         rcases rootFindKVs_sound hH xs ys ha.2 hb.2 he with h | h
         · exact Or.inl (by rw [h])
         · exact Or.inr h)
  · right
    unfold rootFind; rw [if_neg hf]
    exact coll_of_frames hd hf
theorem rootFindList_sound (hH : HashFits H) : ∀ (xs ys : List JVal), TreeAdmList xs →
    TreeAdmList ys → digests H xs = digests H ys → xs = ys ∨ Coll H (rootFindList H xs ys)
  | [], [], _, _, _ => Or.inl rfl
  | [], _ :: _, _, _, h => by simp [digests] at h
  | _ :: _, [], _, _, h => by simp [digests] at h
  | x :: xs, y :: ys, ha, hb, h => by
    simp only [digests, List.cons.injEq] at h
    simp only [rootFindList]
    split
    · rename_i hxy
      rcases rootFindList_sound hH xs ys ha.2 hb.2 h.2 with h' | h'
      · exact Or.inl (by rw [hxy, h'])
      · exact Or.inr h'
    · rename_i hxy
      rcases rootFind_sound hH x y ha.1 hb.1 h.1 with h' | h'
      · exact absurd h' hxy
      · exact Or.inr h'
theorem rootFindKVs_sound (hH : HashFits H) : ∀ (xs ys : List (List UInt8 × JVal)),
    TreeAdmKVs xs → TreeAdmKVs ys → digestKVs H xs = digestKVs H ys →
    xs = ys ∨ Coll H (rootFindKVs H xs ys)
  | [], [], _, _, _ => Or.inl rfl
  | [], _ :: _, _, _, h => by simp [digestKVs] at h
  | _ :: _, [], _, _, h => by simp [digestKVs] at h
  | (k, x) :: xs, (k', y) :: ys, ha, hb, h => by
    simp only [digestKVs, List.cons.injEq, Prod.mk.injEq] at h
    simp only [rootFindKVs]
    split
    · rename_i hxy
      rcases rootFindKVs_sound hH xs ys ha.2.2 hb.2.2 h.2 with h' | h'
      · exact Or.inl (by rw [hxy, h', h.1.1])
      · exact Or.inr h'
    · rename_i hxy
      rcases rootFind_sound hH x y ha.2.1 hb.2.1 h.1.2 with h' | h'
      · exact absurd h' hxy
      · exact Or.inr h'
end

end

/-! ## Openings -/

/-- A single-path opening (see the module header). -/
inductive Opening where
  | here (v : JVal)
  | arr (ds : List Digest) (rest : Opening)
  | obj (es : List (List UInt8 × Digest)) (rest : Opening)
  | absentArr (ds : List Digest)
  | absentObj (es : List (List UInt8 × Digest))
  deriving Repr, Inhabited

/-- The first entry with key `k` among an opened object's entries. -/
def findKeyD (k : List UInt8) : List (List UInt8 × Digest) → Option Digest
  | [] => none
  | (k', d) :: r => if k' = k then some d else findKeyD k r

section
variable (H : List UInt8 → Digest)

/-- ⚑ **The opening checker.** `some o` means: the opening is consistent with root `d`, and the
value at `p` is `o` (`none` = absent). -/
def walk : Digest → Path → Opening → Option (Option JVal)
  | d, p, .here v =>
    if decide (TreeAdm v) && digest H v == d then some (lookup v p) else none
  | d, .idx i :: p, .arr ds rest =>
    if decide (Frame.arr ds).Adm && H (Frame.arr ds).bytes == d then
      match ds[i]? with
      | some c => walk c p rest
      | none => none
    else none
  | d, .key k :: p, .obj es rest =>
    if decide (Frame.obj es).Adm && H (Frame.obj es).bytes == d then
      match findKeyD k es with
      | some c => walk c p rest
      | none => none
    else none
  | d, s :: _, .absentArr ds =>
    if decide (Frame.arr ds).Adm && H (Frame.arr ds).bytes == d then
      match s with
      | .idx i => if ds.length ≤ i then some none else none
      | .key _ => some none
    else none
  | d, s :: _, .absentObj es =>
    if decide (Frame.obj es).Adm && H (Frame.obj es).bytes == d then
      match s with
      | .key k => if findKeyD k es = none then some none else none
      | .idx _ => some none
    else none
  | _, _, _ => none

/-- **The pair a rejected-in-truth opening collides at**, computed from the named tree and the
opening: the first level whose disclosed frame differs from the tree's own, or `rootFind` at a
disclosed subtree. On an honest opening every pair it returns is equal (no collision). -/
def walkFind : JVal → Path → Opening → List UInt8 × List UInt8
  | t, _, .here v => rootFind H v t
  | t, .idx i :: p, .arr ds rest =>
    if (Frame.arr ds).bytes = (frameOf H t).bytes then
      match t with
      | .arr xs => match xs[i]? with
        | some c => walkFind c p rest
        | none => ([], [])
      | _ => ([], [])
    else ((Frame.arr ds).bytes, (frameOf H t).bytes)
  | t, .key k :: p, .obj es rest =>
    if (Frame.obj es).bytes = (frameOf H t).bytes then
      match t with
      | .obj kvs => match findKey k kvs with
        | some c => walkFind c p rest
        | none => ([], [])
      | _ => ([], [])
    else ((Frame.obj es).bytes, (frameOf H t).bytes)
  | t, _, .absentArr ds => ((Frame.arr ds).bytes, (frameOf H t).bytes)
  | t, _, .absentObj es => ((Frame.obj es).bytes, (frameOf H t).bytes)
  | _, _, _ => ([], [])

end

/-! ### Soundness of the walk -/

section
variable {H : List UInt8 → Digest}

theorem treeAdm_getElem : ∀ {xs : List JVal} {i : Nat} {c : JVal}, TreeAdmList xs →
    xs[i]? = some c → TreeAdm c
  | x :: _, 0, c, h, hc => by simp at hc; rw [← hc]; exact h.1
  | _ :: xs, i + 1, c, h, hc => by simp at hc; exact treeAdm_getElem h.2 hc

theorem treeAdm_findKey : ∀ {kvs : List (List UInt8 × JVal)} {k : List UInt8} {c : JVal},
    TreeAdmKVs kvs → findKey k kvs = some c → TreeAdm c
  | [], _, _, _, hc => by simp [findKey] at hc
  | (k', v) :: kvs, k, c, h, hc => by
    simp only [findKey] at hc
    split at hc
    · cases hc; exact h.2.1
    · exact treeAdm_findKey h.2.2 hc

theorem findKeyD_digestKVs : ∀ (kvs : List (List UInt8 × JVal)) (k : List UInt8),
    findKeyD k (digestKVs H kvs) = (findKey k kvs).map (digest H)
  | [], _ => rfl
  | (k', v) :: kvs, k => by
    simp only [digestKVs, findKeyD, findKey]
    split <;> simp [findKeyD_digestKVs kvs k]

/-- The disclosed frame equals the tree's, or the two collide. -/
theorem frame_eq_or_coll {f : Frame} {t : JVal} (hd : H f.bytes = digest H t)
    : f.bytes = (frameOf H t).bytes ∨ Coll H (f.bytes, (frameOf H t).bytes) := by
  by_cases e : f.bytes = (frameOf H t).bytes
  · exact Or.inl e
  · exact Or.inr ⟨e, by rw [hd, digest_eq_frame]⟩

/-- ⚑ **`walk_sound`** — an accepted opening against a named tree's digest reports the tree's
true value at the path (or its absence), unless `H` collides at the pair `walkFind` names. -/
theorem walk_sound (hH : HashFits H) : ∀ (p : Path) (op : Opening) (t : JVal) (o : Option JVal),
    TreeAdm t → walk H (digest H t) p op = some o → o = lookup t p ∨ Coll H (walkFind H t p op)
  | p, .here v, t, o, ht, h => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    split at h
    · rename_i hc
      cases h
      rcases rootFind_sound hH v t hc.1 ht hc.2 with e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr (by simp only [walkFind]; exact e)
    · cases h
  | .idx i :: p, .arr ds rest, t, o, ht, h => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    split at h
    · rename_i hc
      rcases frame_eq_or_coll hc.2 with e | e
      · have hf := Frame.bytes_injective hc.1 (frameOf_adm hH t ht) e
        cases t with
        | arr xs =>
          simp only [frameOf, Frame.arr.injEq] at hf
          subst hf
          simp only [walkFind, frameOf, if_true]
          rw [digests_getElem?] at h
          cases hx : xs[i]? with
          | none => simp [hx] at h
          | some c =>
            simp only [hx, Option.map_some] at h
            have := walk_sound hH p rest c o (treeAdm_getElem ht.2 hx) h
            simpa [lookup, hx] using this
        | _ => all_goals (simp [frameOf] at hf)
      · right; simp only [walkFind]; rw [if_neg e.1]; exact e
    · cases h
  | .key k :: p, .obj es rest, t, o, ht, h => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    split at h
    · rename_i hc
      rcases frame_eq_or_coll hc.2 with e | e
      · have hf := Frame.bytes_injective hc.1 (frameOf_adm hH t ht) e
        cases t with
        | obj kvs =>
          simp only [frameOf, Frame.obj.injEq] at hf
          subst hf
          simp only [walkFind, frameOf, if_true]
          rw [findKeyD_digestKVs] at h
          cases hx : findKey k kvs with
          | none => simp [hx] at h
          | some c =>
            simp only [hx, Option.map_some] at h
            have := walk_sound hH p rest c o (treeAdm_findKey ht.2 hx) h
            simpa [lookup, hx] using this
        | _ => all_goals (simp [frameOf] at hf)
      · right; simp only [walkFind]; rw [if_neg e.1]; exact e
    · cases h
  | s :: p, .absentArr ds, t, o, ht, h => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    split at h
    · rename_i hc
      rcases frame_eq_or_coll hc.2 with e | e
      · have hf := Frame.bytes_injective hc.1 (frameOf_adm hH t ht) e
        left
        cases t with
        | arr xs =>
          simp only [frameOf, Frame.arr.injEq] at hf
          subst hf
          cases s with
          | idx i =>
            simp only at h
            split at h
            · rename_i hi
              cases h
              rw [digests_length] at hi
              simp [lookup, List.getElem?_eq_none hi]
            · cases h
          | key k => cases h; simp [lookup]
        | _ => all_goals (simp [frameOf] at hf)
      · right; simp only [walkFind]; exact e
    · cases h
  | s :: p, .absentObj es, t, o, ht, h => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    split at h
    · rename_i hc
      rcases frame_eq_or_coll hc.2 with e | e
      · have hf := Frame.bytes_injective hc.1 (frameOf_adm hH t ht) e
        left
        cases t with
        | obj kvs =>
          simp only [frameOf, Frame.obj.injEq] at hf
          subst hf
          cases s with
          | key k =>
            simp only at h
            split at h
            · rename_i hk
              cases h
              rw [findKeyD_digestKVs] at hk
              cases hx : findKey k kvs with
              | none => simp [lookup, hx]
              | some c => simp [hx] at hk
            · cases h
          | idx i => cases h; simp [lookup]
        | _ => all_goals (simp [frameOf] at hf)
      · right; simp only [walkFind]; exact e
    · cases h
  | [], .arr _ _, _, _, _, h => by simp [walk] at h
  | [], .obj _ _, _, _, _, h => by simp [walk] at h
  | [], .absentArr _, _, _, _, h => by simp [walk] at h
  | [], .absentObj _, _, _, _, h => by simp [walk] at h
  | .key _ :: _, .arr _ _, _, _, _, h => by simp [walk] at h
  | .idx _ :: _, .obj _ _, _, _, _, h => by simp [walk] at h

end

/-! ## The honest prover, and completeness -/

section
variable (H : List UInt8 → Digest)

/-- The honest opening of `t` at `p`. -/
def openAt : JVal → Path → Opening
  | v, [] => .here v
  | .arr xs, .idx i :: p =>
    match xs[i]? with
    | some c => .arr (digests H xs) (openAt c p)
    | none => .absentArr (digests H xs)
  | .arr xs, .key _ :: _ => .absentArr (digests H xs)
  | .obj kvs, .key k :: p =>
    match findKey k kvs with
    | some c => .obj (digestKVs H kvs) (openAt c p)
    | none => .absentObj (digestKVs H kvs)
  | .obj kvs, .idx _ :: _ => .absentObj (digestKVs H kvs)
  | v, _ :: _ => .here v

end

section
variable {H : List UInt8 → Digest}

/-- ⚑ **Completeness**: the honest opening of an admitted tree is accepted, with the true value. -/
theorem walk_openAt (hH : HashFits H) : ∀ (t : JVal) (p : Path), TreeAdm t →
    walk H (digest H t) p (openAt H t p) = some (lookup t p)
  | t, [], ht => by
    cases t <;> simp [openAt, walk, ht, lookup]
  | .arr xs, .idx i :: p, ht => by
    have hadm := frameOf_adm hH (.arr xs) ht
    simp only [frameOf] at hadm
    cases hx : xs[i]? with
    | none =>
      simp only [openAt, hx, walk, hadm, decide_true, digest, beq_self_eq_true, Bool.and_self,
        if_true, lookup]
      rw [if_pos (by rw [digests_length]; exact List.getElem?_eq_none_iff.mp hx)]
    | some c =>
      simp only [openAt, hx, walk, hadm, decide_true, digest, beq_self_eq_true, Bool.and_self,
        if_true, lookup, digests_getElem?, Option.map_some]
      exact walk_openAt hH c p (treeAdm_getElem ht.2 hx)
  | .arr xs, .key k :: p, ht => by
    have hadm := frameOf_adm hH (.arr xs) ht
    simp only [frameOf] at hadm
    simp [openAt, walk, hadm, digest, lookup]
  | .obj kvs, .key k :: p, ht => by
    have hadm := frameOf_adm hH (.obj kvs) ht
    simp only [frameOf] at hadm
    cases hx : findKey k kvs with
    | none =>
      simp [openAt, hx, walk, hadm, digest, lookup, findKeyD_digestKVs]
    | some c =>
      simp only [openAt, hx, walk, hadm, decide_true, digest, beq_self_eq_true, Bool.and_self,
        if_true, lookup, findKeyD_digestKVs, Option.map_some]
      exact walk_openAt hH c p (treeAdm_findKey ht.2 hx)
  | .obj kvs, .idx i :: p, ht => by
    have hadm := frameOf_adm hH (.obj kvs) ht
    simp only [frameOf] at hadm
    simp [openAt, walk, hadm, digest, lookup]
  | .null, _ :: _, ht | .bool _, _ :: _, ht | .int _, _ :: _, ht | .dec _ _, _ :: _, ht
  | .str _, _ :: _, ht => by
    simp [openAt, walk, ht, lookup]

end

/-! ## The executable instance: SHAKE256 with a domain prefix

The deployed leaf hashes with cSHAKE256 (minidregg `Tower256CshakeMerkle*`); SHAKE256 with a
domain-separation prefix stands in for it here, as in `DatalogCheck`. Every theorem above is
abstract in `H`; only these pins and the executable fix it. -/

/-- The node hash: `SHAKE256("dregg.tree.node.v1" ‖ 0x00 ‖ frame, 32)`. -/
def shakeH (x : List UInt8) : Digest :=
  Dregg2.Crypto.Keccak.shake256 ("dregg.tree.node.v1".toUTF8.toList ++ [0] ++ x) 32

theorem shakeH_fits : HashFits shakeH := by
  intro x
  have : (shakeH x).length ≤ 32 := by
    simp only [shakeH, Dregg2.Crypto.Keccak.shake256, Dregg2.Crypto.Keccak.squeeze]
    exact List.length_take_le _ _
  omega

/-! ## Falsifiers -/

namespace Falsifier

private def k (s : String) : List UInt8 := s.toUTF8.toList

/-- A tool-call-shaped record. -/
def rec1 : JVal := .obj [(k "input", .obj [(k "command", .str (k "ls -la")), (k "timeout", .int 120000)]),
  (k "name", .str (k "Bash"))]

def pCmd : Path := [.key (k "input"), .key (k "command")]
def pDesc : Path := [.key (k "input"), .key (k "description")]

-- honest openings: present, absent key, index on an object, path through a scalar
#guard walk shakeH (digest shakeH rec1) pCmd (openAt shakeH rec1 pCmd) == some (some (.str (k "ls -la")))
#guard walk shakeH (digest shakeH rec1) pDesc (openAt shakeH rec1 pDesc) == some none
#guard walk shakeH (digest shakeH rec1) [.idx 0] (openAt shakeH rec1 [.idx 0]) == some none
#guard walk shakeH (digest shakeH rec1) (pCmd ++ [.idx 0]) (openAt shakeH rec1 (pCmd ++ [.idx 0])) == some none

/- **Wrong path opened.** The opening built for `input.command` presented as an opening of
`input.description`: the key the path names is looked up in the disclosed entries, so it is
refused (it would otherwise "prove" the description is `ls -la`). -/
#guard walk shakeH (digest shakeH rec1) pDesc (openAt shakeH rec1 pCmd) == none

/-- **A sibling swapped.** Exchanging two disclosed sibling digests changes the frame, so the
recomputed root misses. -/
def swapped : Opening :=
  match openAt shakeH rec1 pCmd with
  | .obj [(a, da), (b, db)] rest => .obj [(a, db), (b, da)] rest
  | o => o
#guard walk shakeH (digest shakeH rec1) pCmd swapped == none

/-- **Absence claimed for a present key.** An `absentObj` at `input` whose entries are the true
ones is refused because `command` is among them; one whose entries drop `command` misses the root. -/
def inputEntries : List (List UInt8 × Digest) :=
  match rec1 with
  | .obj [(_, v), _] => match v with
    | .obj kvs => digestKVs shakeH kvs
    | _ => []
  | _ => []
#guard walk shakeH (digest shakeH rec1) pCmd
  (.obj (digestKVs shakeH (match rec1 with | .obj kvs => kvs | _ => [])) (.absentObj inputEntries)) == none
#guard walk shakeH (digest shakeH rec1) pCmd
  (.obj (digestKVs shakeH (match rec1 with | .obj kvs => kvs | _ => []))
    (.absentObj (inputEntries.filter (·.1 != k "command")))) == none

/-- **The tagless frame (the weaker commitment).** Drop the kind discriminator and frame an
object's entries as an array of pairs: `[]` and `{}` then have one digest, and the weaker walk
accepts "the record is `{}`" (an object, so a schema demanding `type: object` would pass) against
the root of `[]`. The real frames refuse it. -/
def weakItem : Frame → Item
  | .leaf v => toItem v
  | .arr ds => .arr (ds.map .bytes)
  | .obj es => .arr (es.map fun e => .arr [.text e.1, .bytes e.2])
def weakDigest (v : JVal) : Digest := shakeH (enc (weakItem (frameOf shakeH v)))

#guard weakDigest (.arr []) == weakDigest (.obj [])
#guard digest shakeH (.arr []) != digest shakeH (.obj [])
#guard walk shakeH (digest shakeH (.arr [])) [] (.here (.obj [])) == none

end Falsifier

/-- info: 'Dregg2.Tree.rootFind_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rootFind_sound

/-- info: 'Dregg2.Tree.walk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms walk_sound

/-- info: 'Dregg2.Tree.walk_openAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms walk_openAt

end Dregg2.Tree
