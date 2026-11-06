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

/-- What `presentation.verify()` returned for one presentation. -/
structure Evidence where
  presentation : ByteArray
  serverName   : String
  notaryKey    : String
  sent         : ByteArray
  recv         : ByteArray

/-- The verifier's policy: pinned notary keys (hex SEC1) and allowed server names. -/
structure Policy where
  notaries : List String
  hosts    : List String

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

/-- **The deployed hop predicate.** -/
def deployedV (rows : List Row) (pol : Policy) (h : Hop) (kr : Int) : Bool :=
  if h.kind == 0 then h.att == 0 && h.host == 0 else
  match rows.find? (fun r => r.att == h.att) with
  | none => false
  | some r =>
      r.host == h.host && r.req == h.req && r.resp == h.resp &&
      pol.notaries.contains r.ev.notaryKey && pol.hosts.contains r.ev.serverName &&
      (h.kind == 1 || (h.kind == 2 && containsBytes r.ev.recv (hex64 kr).toUTF8))

/-- **The deployed verifier**: `CallTreeCore.verify` at `deployedV` and `treeHash`. -/
def deployedVerify (evs : List Evidence) (pol : Policy) (root : Int) (t : CallTree) : Bool :=
  verify (deployedV (table evs) pol) treeHash root t

end Dregg2.Lightclient.CallTreeDeploy
