/-
# Dregg2.Lightclient.CallTreeDeploy — the deployed hash and hop predicate (Lean core only).

* `treeHash` — the `hash : List Int → Int` the deployed tree is committed under:
  `BLAKE3("dregg-calltree-v1" ‖ u32 count ‖ enc x₁ ‖ … ‖ enc xₙ)` read big-endian as a natural number,
  where `enc x = sign ‖ u32 len ‖ |x| big-endian minimal`. The encoding is injective on `List Int`,
  so a `SpongeColl treeHash p` at a pair `CallTree.treeFind` names is a BLAKE3-256 collision.
* `digestBytes tag b` — the digests a hop carries: `BLAKE3("dregg-calltree-bytes-v1:" ‖ tag ‖ 0 ‖ b)`.
* `deployedV table pol` — the hop predicate the checker runs. A local node (kind 0) must carry
  `att = host = 0`. A transport hop must name, by its `att` digest, a presentation whose verified
  extract (server name, notary key, authenticated sent and received bytes) digests to exactly the
  hop's `host`, `req`, `resp`; the notary key must be pinned by the policy and the server name
  allowed; a kind-2 hop (a callee that records its own calls) must ALSO carry its children root,
  as 64 lowercase hex characters, inside the authenticated response.

Trust: `Evidence` is what `presentation.verify()` returned for `presentation` (Rust, tlsn alpha.15).
Every comparison after that is this file. BLAKE3 is `Dregg2.Crypto.Blake3Compute` (KAT-pinned).
-/
import Dregg2.Lightclient.CallTreeCore
import Dregg2.Crypto.Blake3Compute

namespace Dregg2.Lightclient.CallTreeDeploy

open Dregg2.Lightclient.CallTreeCore

def u32be (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
     UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]⟩

/-- Minimal big-endian bytes of a natural number (`0 ↦ []`). -/
def natBE (n : Nat) : ByteArray :=
  let rec go (n : Nat) (acc : List UInt8) (fuel : Nat) : List UInt8 :=
    match fuel with
    | 0 => acc
    | fuel + 1 => if n = 0 then acc else go (n / 256) (UInt8.ofNat (n % 256) :: acc) fuel
  ⟨(go n [] (n.log2 / 8 + 2)).toArray⟩

def ofBE (b : ByteArray) : Nat := b.foldl (fun a x => a * 256 + x.toNat) 0

def encInt (x : Int) : ByteArray :=
  let m := natBE x.natAbs
  ByteArray.mk #[if x < 0 then 1 else 0] ++ u32be m.size ++ m

def treeDomain : ByteArray := "dregg-calltree-v1".toUTF8

def encList (xs : List Int) : ByteArray :=
  xs.foldl (fun acc x => acc ++ encInt x) (treeDomain ++ u32be xs.length)

/-- The deployed tree hash. -/
def treeHash (xs : List Int) : Int := Int.ofNat (ofBE (Dregg2.Crypto.Blake3.hash (encList xs)))

/-- The deployed byte digest. -/
def digestBytes (tag : String) (b : ByteArray) : Int :=
  Int.ofNat (ofBE (Dregg2.Crypto.Blake3.hash
    ("dregg-calltree-bytes-v1:".toUTF8 ++ tag.toUTF8 ++ ByteArray.mk #[0] ++ b)))

/-- A 256-bit value as 64 lowercase hex characters. -/
def hex64 (x : Int) : String :=
  let b := natBE x.toNat
  let pad := ByteArray.mk (Array.replicate (32 - min 32 b.size) 0)
  Dregg2.Crypto.Blake3.toHex (pad ++ b)

/-- `needle` occurs in `hay`. -/
def containsBytes (hay needle : ByteArray) : Bool :=
  let n := needle.size
  if n = 0 then true else
  (List.range (hay.size + 1 - n)).any fun i =>
    (List.range n).all fun j => hay.get! (i + j) == needle.get! j

/-- What `presentation.verify()` returned for one presentation. Bytes the presentation did NOT
authenticate are `0x00` in `sent`/`recv` (the extractor's mask), so every byte check below that
refuses a `0x00` byte only ever matches authenticated bytes. -/
structure Evidence where
  presentation : ByteArray
  serverName   : String
  notaryKey    : String
  sent         : ByteArray
  recv         : ByteArray
  /-- The connection time the notary attested (unix seconds). -/
  time         : Nat
  /-- The signed attestation's identity (hex of its header: id, version, field root): one notarised
  session, however many presentations (disclosures, encodings) are cut from it. -/
  session      : String

/-- The verifier's policy: pinned notary keys (`alg:hex`), allowed server names, the servers that
may appear as recording callees (kind 2), the window every hop's attested connection time must fall
in, and the dataflow edges that must be present, as (edge kind, source server, destination server). -/
structure Policy where
  notaries : List String
  hosts    : List String
  recorders : List String
  timeLo   : Nat
  timeHi   : Nat
  requireEdges : List (Nat × String × String)

/-- One evidence entry with its digests computed (in Lean). -/
structure Row where
  att  : Int
  host : Int
  req  : Int
  resp : Int
  ev   : Evidence

def Row.of (e : Evidence) : Row :=
  { att := digestBytes "att" e.presentation, host := digestBytes "host" e.serverName.toUTF8,
    req := digestBytes "req" e.sent, resp := digestBytes "resp" e.recv, ev := e }

def table (evs : List Evidence) : List Row := evs.map Row.of

/-- No `0x00` (masked) byte. -/
def unmasked (b : ByteArray) : Bool := b.data.all (· != 0)

/-- The HTTP body: everything after the first `CRLF CRLF` (empty if there is none). -/
def httpBody (b : ByteArray) : ByteArray :=
  let n := b.size
  match (List.range n).find? (fun i => i + 3 < n && b.get! i == 13 && b.get! (i+1) == 10 &&
      b.get! (i+2) == 13 && b.get! (i+3) == 10) with
  | some i => b.extract (i + 4) n
  | none => ByteArray.empty

/-- `needle` (non-empty, unmasked) occurs in the HTTP body of `hay`. -/
def inBody (hay needle : ByteArray) : Bool :=
  needle.size != 0 && unmasked needle && containsBytes (httpBody hay) needle

/-- The designated field a recording callee returns its subtree root in. -/
def rootField (kr : Int) : ByteArray := ("\"subtree_root\":\"" ++ hex64 kr ++ "\"").toUTF8

/-- **The deployed hop predicate.** A local node carries no transport. A transport hop must be backed
by evidence whose digests are exactly the hop's, under a pinned notary, an allowed host and the time
window. Kind 1 is a LEAF (its children root is the empty MMR's). Kind 2 is allowed only for a
policy-listed recording callee, and its authenticated response body carries its children root in the
designated field `"subtree_root":"<hex>"`. -/
def deployedV (rows : List Row) (pol : Policy) (h : Hop) (kr : Int) : Bool :=
  if h.kind == 0 then h.att == 0 && h.host == 0 else
  match rows.find? (fun r => r.att == h.att) with
  | none => false
  | some r =>
      r.host == h.host && r.req == h.req && r.resp == h.resp &&
      pol.notaries.contains r.ev.notaryKey && pol.hosts.contains r.ev.serverName &&
      decide (pol.timeLo ≤ r.ev.time) && decide (r.ev.time ≤ pol.timeHi) &&
      ((h.kind == 1 && kr == mrootC treeHash []) ||
       (h.kind == 2 && pol.recorders.contains r.ev.serverName &&
          inBody r.ev.recv (rootField kr)))

mutual
/-- The attestation digests of every transport hop, preorder. -/
def atts : CallTree → List Int
  | .node h ks => (if h.kind == 0 then [] else [h.att]) ++ attsL ks
def attsL : List CallTree → List Int
  | [] => []
  | k :: ks => atts k ++ attsL ks
end

mutual
/-- (child att, parent att) for every transport hop whose parent is a transport hop. -/
def parentPairs : CallTree → List (Int × Int)
  | .node h ks =>
      (if h.kind == 0 then [] else ks.map (fun k => (k.hop.att, h.att))) ++ parentPairsL ks
def parentPairsL : List CallTree → List (Int × Int)
  | [] => []
  | k :: ks => parentPairs k ++ parentPairsL ks
end

/-- No element twice (decidable, core-only). -/
def nodupB {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-- The signed sessions behind the tree's transport hops. -/
def sessions (rows : List Row) (t : CallTree) : List String :=
  (atts t).filterMap fun a => (rows.find? (fun r => r.att == a)).map (·.ev.session)

/-- A dataflow edge between two hops named by attestation digest. `kind 0`: `bytes` occur in the
authenticated response BODY of `src` and the authenticated request BODY of `dst`, and `src` precedes
`dst` in the tree (what one call returned was sent on by a later call). `kind 1`: `bytes` occur in
the authenticated response BODY of `src` and of `dst`, and `dst` is `src`'s PARENT (a callee's
attested fetch is carried in the caller's attested result). -/
structure Edge where
  kind  : Nat
  src   : Int
  dst   : Int
  bytes : ByteArray

/-- The shortest span an edge may carry: shorter spans occur by accident. -/
def minEdgeBytes : Nat := 16

def indexOf (l : List Int) (x : Int) : Option Nat := l.findIdx? (· == x)

def edgeOk (rows : List Row) (t : CallTree) (e : Edge) : Bool :=
  let order := atts t
  decide (minEdgeBytes ≤ e.bytes.size) &&
  match rows.find? (fun r => r.att == e.src), rows.find? (fun r => r.att == e.dst),
        indexOf order e.src, indexOf order e.dst with
  | some a, some b, some i, some j =>
      inBody a.ev.recv e.bytes &&
      (if e.kind == 0 then decide (i < j) && inBody b.ev.sent e.bytes
       else e.kind == 1 && (parentPairs t).contains (e.src, e.dst) && inBody b.ev.recv e.bytes)
  | _, _, _, _ => false

def serverOf (rows : List Row) (att : Int) : Option String :=
  (rows.find? (fun r => r.att == att)).map (·.ev.serverName)

/-- Every listed edge holds, and every edge the policy requires is witnessed by one of them. -/
def edgesOk (rows : List Row) (pol : Policy) (t : CallTree) (es : List Edge) : Bool :=
  es.all (edgeOk rows t) &&
  pol.requireEdges.all fun (k, a, b) =>
    es.any fun e => e.kind == k && serverOf rows e.src == some a && serverOf rows e.dst == some b

/-- **The deployed verifier**: `CallTreeCore.verify` at `deployedV` and `treeHash`, plus: no signed
session (and no presentation) backs two hops, and the dataflow edges hold. -/
def deployedVerify (evs : List Evidence) (pol : Policy) (root : Int) (t : CallTree)
    (es : List Edge) : Bool :=
  verify (deployedV (table evs) pol) treeHash root t && nodupB (atts t) &&
    nodupB (sessions (table evs) t) && edgesOk (table evs) pol t es

/-- Everything proved about `CallTreeCore.verify` (`CallTree.verify_sound`, `no_omission`,
`verify_attested`) applies to an accepting deployed verifier. -/
theorem deployedVerify_verify {evs pol root t es} (h : deployedVerify evs pol root t es = true) :
    verify (deployedV (table evs) pol) treeHash root t = true := by
  simp only [deployedVerify, Bool.and_eq_true] at h
  exact h.1.1.1

end Dregg2.Lightclient.CallTreeDeploy

/-! ## The deployment bridge: a `treeHash` collision is a BLAKE3 collision.

`Blake3.hash` always returns 32 bytes; `ofBE` is injective on byte strings of one length; `encList`
is injective on lists whose length and every element's magnitude byte-count fit the 4-byte length
prefixes. So two distinct lists with one `treeHash` are two distinct BLAKE3 inputs with one output. -/

namespace Dregg2.Crypto.Blake3
theorem g_size (st : Array UInt32) (a b c d : Nat) (mx my : UInt32) :
    (g st a b c d mx my).size = st.size := by
  simp [g]

theorem roundFn_size (st m : Array UInt32) : (roundFn st m).size = st.size := by
  simp [roundFn, g_size]

theorem rounds_size : ∀ (n : Nat) (st m : Array UInt32), (rounds n st m).size = st.size
  | 0, _, _ => rfl
  | n + 1, st, m => by rw [rounds, rounds_size n, roundFn_size]

theorem compress_size (cv block : Array UInt32) (counter : UInt64) (blockLen flags : UInt32) :
    (compress cv block counter blockLen flags).size = 16 := by
  have h : ∀ (l : List Nat) (s : Array UInt32),
      (l.foldl (fun (s : Array UInt32) i =>
        (s.set! i (s[i]! ^^^ s[i + 8]!)).set! (i + 8) (s[i + 8]! ^^^ cv[i]!)) s).size = s.size := by
    intro l; induction l with
    | nil => intro s; rfl
    | cons a t ih => intro s; rw [List.foldl_cons, ih]; simp
  simp only [compress]
  rw [h, rounds_size]; rfl

theorem fold_u32le_size (ws : Array UInt32) (acc : ByteArray) :
    (ws.foldl (fun a w => a ++ u32le w) acc).size = acc.size + 4 * ws.size := by
  rw [← Array.foldl_toList]
  have : ∀ (l : List UInt32) (acc : ByteArray),
      (l.foldl (fun a w => a ++ u32le w) acc).size = acc.size + 4 * l.length := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons a t ih =>
      intro acc; rw [List.foldl_cons, ih]
      have h4 : (u32le a).size = 4 := rfl
      rw [ByteArray.size_append, h4, List.length_cons]; omega
  rw [this]; simp

theorem rootBytes_size (o : Output) (len : Nat) : (o.rootBytes len).size = len := by
  have h : ∀ (l : List Nat) (acc : ByteArray),
      (l.foldl (fun acc i =>
        (compress o.inputCv o.blockWords (UInt64.ofNat i) o.blockLen (o.flags ||| ROOT)).foldl
          (fun a w => a ++ u32le w) acc) acc).size = acc.size + 64 * l.length := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons a t ih =>
      intro acc; rw [List.foldl_cons, ih, fold_u32le_size, compress_size]
      simp; omega
  simp only [Output.rootBytes]
  rw [ByteArray.size_extract, h]
  simp; omega

theorem hash_size (b : ByteArray) : (hash b).size = 32 := rootBytes_size _ _

end Dregg2.Crypto.Blake3

namespace Dregg2.Lightclient.CallTreeDeploy

theorem bytes_foldl_eq {β : Type} (f : β → UInt8 → β) (init : β) (b : ByteArray) :
    b.foldl f init = b.data.toList.foldl f init := by
  have key : ∀ i j (acc : β), i + j = b.size →
      ByteArray.foldlM.loop (m := Id) (fun a x => pure (f a x)) b b.size (Nat.le_refl _) i j acc
        = (b.data.toList.drop j).foldl f acc := by
    intro i
    induction i with
    | zero =>
      intro j acc h
      unfold ByteArray.foldlM.loop
      have hsz : b.data.size = b.size := rfl
      have : b.data.toList.drop j = [] := by
        simp [List.drop_eq_nil_iff]; omega
      rw [this]; split <;> rfl
    | succ i ih =>
      intro j acc h
      unfold ByteArray.foldlM.loop
      have hj : j < b.size := by omega
      rw [dif_pos hj]
      have hd : b.data.toList.drop j = b[j] :: b.data.toList.drop (j+1) := by
        rw [← List.getElem_cons_drop (by simpa [← ByteArray.size_data] using hj)]
        simp [ByteArray.getElem_eq_getElem_data]
        rfl
      rw [hd, List.foldl_cons, ← ih (j+1) (f acc b[j]) (by omega)]
      rfl
  simp only [ByteArray.foldl, ByteArray.foldlM, Nat.le_refl, dif_pos, Nat.sub_zero]
  exact (key b.size 0 init (by omega)).trans (by simp)

/-- List-level big-endian reading. -/
def ofBEL (l : List UInt8) : Nat := l.foldl (fun a x => a * 256 + x.toNat) 0

theorem ofBE_eq (b : ByteArray) : ofBE b = ofBEL b.data.toList := bytes_foldl_eq _ _ _

theorem foldl_be (l : List UInt8) (c : Nat) :
    l.foldl (fun a x => a * 256 + x.toNat) c = c * 256 ^ l.length + ofBEL l := by
  induction l generalizing c with
  | nil => simp [ofBEL]
  | cons a t ih =>
    simp only [List.foldl_cons, ofBEL, List.length_cons]
    rw [ih, ih (0 * 256 + a.toNat), Nat.pow_succ]
    simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm 256]

theorem ofBEL_cons (a : UInt8) (t : List UInt8) :
    ofBEL (a :: t) = a.toNat * 256 ^ t.length + ofBEL t := by
  show List.foldl _ _ _ = _
  rw [List.foldl_cons, foldl_be]; simp

theorem ofBEL_append_single (l : List UInt8) (a : UInt8) :
    ofBEL (l ++ [a]) = ofBEL l * 256 + a.toNat := by
  simp [ofBEL, List.foldl_append]

theorem ofBEL_lt (l : List UInt8) : ofBEL l < 256 ^ l.length := by
  induction l with
  | nil => simp [ofBEL]
  | cons a t ih =>
    rw [ofBEL_cons, List.length_cons, Nat.pow_succ']
    have ha : a.toNat < 256 := a.toNat_lt
    have : a.toNat * 256 ^ t.length + ofBEL t < (a.toNat + 1) * 256 ^ t.length := by
      rw [Nat.add_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (by omega))

theorem ofBEL_inj : ∀ (l m : List UInt8), l.length = m.length → ofBEL l = ofBEL m → l = m
  | [], [], _, _ => rfl
  | a :: t, b :: s, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [ofBEL_cons, ofBEL_cons, hl] at h
    have ht := ofBEL_lt t; have hs := ofBEL_lt s; rw [hl] at ht
    have hp : 0 < 256 ^ s.length := Nat.pow_pos (by decide)
    have e1 : (a.toNat * 256 ^ s.length + ofBEL t) / 256 ^ s.length = a.toNat := by
      rw [Nat.mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt ht, Nat.add_zero]
    have e2 : (b.toNat * 256 ^ s.length + ofBEL s) / 256 ^ s.length = b.toNat := by
      rw [Nat.mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt hs, Nat.add_zero]
    have hab : a.toNat = b.toNat := by rw [← e1, ← e2, h]
    have hts : ofBEL t = ofBEL s := by
      rw [hab] at h; omega
    rw [UInt8.toNat_inj.mp hab, ofBEL_inj t s hl hts]

theorem ofBE_injective_of_size {a b : ByteArray} (hs : a.size = b.size) (h : ofBE a = ofBE b) :
    a = b := by
  rw [ofBE_eq, ofBE_eq] at h
  have hl : a.data.toList.length = b.data.toList.length := by simpa using hs
  have := ofBEL_inj _ _ hl h
  cases a; cases b; simp_all


theorem natBE_go_acc : ∀ (fuel n : Nat) (acc : List UInt8),
    natBE.go n acc fuel = natBE.go n [] fuel ++ acc
  | 0, n, acc => rfl
  | fuel + 1, n, acc => by
    simp only [natBE.go]
    split
    · rfl
    · rw [natBE_go_acc fuel _ (_ :: acc), natBE_go_acc fuel _ [_]]; simp

theorem ofBEL_natBE_go : ∀ (fuel n : Nat), n < 256 ^ fuel → ofBEL (natBE.go n [] fuel) = n
  | 0, n, h => by simp at h; subst h; rfl
  | fuel + 1, n, h => by
    simp only [natBE.go]
    split
    · next h0 => subst h0; rfl
    · rw [natBE_go_acc, ofBEL_append_single, ofBEL_natBE_go fuel (n / 256) ?_]
      · have : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
          simp
        rw [this]; omega
      · rw [Nat.pow_succ] at h
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)

theorem natBE_fuel (n : Nat) : n < 256 ^ (n.log2 / 8 + 2) := by
  have h1 := @Nat.lt_log2_self n
  have h2 : 2 ^ (n.log2 + 1) ≤ 2 ^ (8 * (n.log2 / 8 + 2)) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : (2 : Nat) ^ (8 * (n.log2 / 8 + 2)) = 256 ^ (n.log2 / 8 + 2) := by
    rw [Nat.pow_mul]
  omega

/-- The bytes of `natBE n`, as a list. -/
theorem natBE_data (n : Nat) : (natBE n).data.toList = natBE.go n [] (n.log2 / 8 + 2) := by
  simp [natBE]

theorem ofBE_natBE (n : Nat) : ofBE (natBE n) = n := by
  rw [ofBE_eq, natBE_data]; exact ofBEL_natBE_go _ _ (natBE_fuel n)

theorem u32be_data (n : Nat) : (u32be n).data.toList =
    [UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
     UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)] := rfl

theorem u32be_inj {n m : Nat} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32)
    (h : (u32be n).data.toList = (u32be m).data.toList) : n = m := by
  rw [u32be_data, u32be_data] at h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : ∀ a b : Nat, UInt8.ofNat (a % 256) = UInt8.ofNat (b % 256) → a % 256 = b % 256 := by
    intro a b hab
    have := congrArg UInt8.toNat hab
    simp at this
    omega
  have := e _ _ h1; have := e _ _ h2; have := e _ _ h3; have := e _ _ h4
  omega

/-- The bytes of `encInt x`, as a list. -/
theorem encInt_data (x : Int) : (encInt x).data.toList =
    (if x < 0 then (1 : UInt8) else 0) :: ((u32be (natBE x.natAbs).size).data.toList ++
      (natBE x.natAbs).data.toList) := by
  simp [encInt]

/-- One element decodes off the front: equal encodings followed by anything agree on the element
and on the rest. -/
theorem encInt_cancel {x y : Int} {r s : List UInt8}
    (hx : (natBE x.natAbs).size < 2 ^ 32) (hy : (natBE y.natAbs).size < 2 ^ 32)
    (h : (encInt x).data.toList ++ r = (encInt y).data.toList ++ s) : x = y ∧ r = s := by
  rw [encInt_data, encInt_data] at h
  simp only [List.cons_append, List.cons.injEq, List.append_assoc] at h
  obtain ⟨hsign, h⟩ := h
  obtain ⟨hu, h⟩ := List.append_inj h (by simp [u32be_data])
  have hsz := u32be_inj hx hy hu
  obtain ⟨hm, hrs⟩ := List.append_inj h (by simp [hsz])
  refine ⟨?_, hrs⟩
  have habs : x.natAbs = y.natAbs := by
    rw [← ofBE_natBE x.natAbs, ← ofBE_natBE y.natAbs, ofBE_eq, ofBE_eq, hm]
  by_cases hx0 : x < 0 <;> by_cases hy0 : y < 0 <;> simp [hx0, hy0] at hsign <;> omega

theorem encList_foldl_data (xs : List Int) (a : ByteArray) :
    (xs.foldl (fun acc x => acc ++ encInt x) a).data.toList =
      a.data.toList ++ xs.flatMap (fun x => (encInt x).data.toList) := by
  induction xs generalizing a with
  | nil => simp
  | cons x t ih => rw [List.foldl_cons, ih]; simp

theorem encList_data (xs : List Int) : (encList xs).data.toList =
    treeDomain.data.toList ++ (u32be xs.length).data.toList ++
      xs.flatMap (fun x => (encInt x).data.toList) := by
  rw [encList, encList_foldl_data]; simp

theorem flatMap_encInt_inj : ∀ (xs ys : List Int), xs.length = ys.length →
    (∀ x ∈ xs, (natBE x.natAbs).size < 2 ^ 32) → (∀ y ∈ ys, (natBE y.natAbs).size < 2 ^ 32) →
    xs.flatMap (fun x => (encInt x).data.toList) = ys.flatMap (fun y => (encInt y).data.toList) →
    xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hl, hbx, hby, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨hxy, hr⟩ := encInt_cancel (hbx x (by simp)) (hby y (by simp)) h
    rw [hxy, flatMap_encInt_inj xs ys (by simpa using hl)
      (fun z hz => hbx z (by simp [hz])) (fun z hz => hby z (by simp [hz])) hr]

/-- **The tree encoding is injective** (on lists the 4-byte length prefixes can count). -/
theorem encList_injective {xs ys : List Int}
    (hxl : xs.length < 2 ^ 32) (hyl : ys.length < 2 ^ 32)
    (hxs : ∀ x ∈ xs, (natBE x.natAbs).size < 2 ^ 32) (hys : ∀ y ∈ ys, (natBE y.natAbs).size < 2 ^ 32)
    (h : encList xs = encList ys) : xs = ys := by
  have hd := congrArg (fun b => b.data.toList) h
  simp only [encList_data, List.append_assoc] at hd
  obtain ⟨_, hd⟩ := List.append_inj hd rfl
  obtain ⟨hu, hd⟩ := List.append_inj hd (by simp [u32be_data])
  exact flatMap_encInt_inj xs ys (u32be_inj hxl hyl hu) hxs hys hd

/-- **The deployment bridge.** Two distinct lists (within the encoding's bounds) with one deployed
`treeHash` are two distinct BLAKE3 inputs with one BLAKE3 output: a `SpongeColl treeHash` pair is a
`SpongeColl Blake3.hash` pair, spelled out. -/
theorem treeHash_coll_is_blake3_coll {xs ys : List Int} (hne : xs ≠ ys)
    (heq : treeHash xs = treeHash ys)
    (hxl : xs.length < 2 ^ 32) (hyl : ys.length < 2 ^ 32)
    (hxs : ∀ x ∈ xs, (natBE x.natAbs).size < 2 ^ 32) (hys : ∀ y ∈ ys, (natBE y.natAbs).size < 2 ^ 32) :
    encList xs ≠ encList ys ∧
      Dregg2.Crypto.Blake3.hash (encList xs) = Dregg2.Crypto.Blake3.hash (encList ys) :=
  ⟨fun h => hne (encList_injective hxl hyl hxs hys h),
   ofBE_injective_of_size (by simp only [Dregg2.Crypto.Blake3.hash_size])
     (Int.ofNat.inj heq)⟩

end Dregg2.Lightclient.CallTreeDeploy
