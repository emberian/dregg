/-
# Dregg2.Stream.Hash: the follower's hash instantiation (Lean core + pure-Lean BLAKE3)

`Lightclient.MMR`'s abstract `hash : List ℤ → ℤ`, instantiated with blake3 over an arity-framed
encoding, and an entry's committed value. Shared by `lake exe stream-check` and the theorems that pin
concrete facts about it (`Stream.ClaudePolicy`). Core-only, so the executable links without Mathlib.
-/
import Dregg2.Crypto.Blake3Compute

namespace Dregg2.Stream.Hash

def be32 (x : Int) : ByteArray :=
  let n := x.toNat
  ByteArray.mk <| (List.range 32).reverse.toArray.map fun k => ((n / 256 ^ k) % 256).toUInt8

def bytesToNat (b : ByteArray) : Nat := b.foldl (fun a x => a * 256 + x.toNat) 0

def mmrTag : ByteArray := "dregg-stream-v1:mmr:n".toUTF8
def entryTag : ByteArray := "dregg-stream-v1:entry".toUTF8

def wideTag : ByteArray := "dregg-stream-v1:mmr:w".toUTF8

def natBytes (n : Nat) : List UInt8 :=
  if n = 0 then [] else natBytes (n / 256) ++ [(n % 256).toUInt8]
termination_by n
decreasing_by omega

/-- An unbounded self-delimiting length (LEB128): 7 bits per byte, high bit = more follows. -/
def leb (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else ((n % 128) + 128).toUInt8 :: leb (n / 128)
termination_by n
decreasing_by omega

def be8 (n : Nat) : ByteArray := ByteArray.mk (leb n).toArray

/-- A canonical framing of any integer: sign byte, LEB128 magnitude length, magnitude. -/
def encWide (x : Int) : ByteArray :=
  let mag := natBytes x.natAbs
  (ByteArray.mk #[if x < 0 then 1 else 0]) ++ be8 mag.length ++ ByteArray.mk mag.toArray

def inRange (x : Int) : Bool := 0 ≤ x && x < 2 ^ 256

/-- The MMR hash. The narrow form (one arity byte, 32-byte big-endian inputs) is the one the Rust
producer computes, and the only one an honest log ever reaches (every input is a blake3 output).
Any other input (an integer outside `[0, 2^256)`, or more than 255 inputs) takes a separately tagged,
canonically framed form. The two tags are the same length and differ in their last byte, so neither
message is a prefix-shifted copy of the other; within each form the framing is fixed-width (narrow) or
self-delimiting with unbounded LEB128 lengths (wide), so no length wraps. So two distinct inputs give distinct messages, and the instantiation is
injective on all of `List ℤ` up to a blake3 collision (`Stream.ClaudePolicy.streamHash_forms_differ`
checks the two forms of the same value differ; the injectivity is argued here, not proved). -/
def streamHash (xs : List Int) : Int :=
  let msg :=
    if xs.length < 256 && xs.all inRange then
      xs.foldl (fun acc x => acc ++ be32 x) (mmrTag.push xs.length.toUInt8)
    else
      xs.foldl (fun acc x => acc ++ encWide x) (wideTag ++ be8 xs.length)
  Int.ofNat <| bytesToNat <| Dregg2.Crypto.Blake3.hash msg

def entryVal (line : ByteArray) : Int := Int.ofNat <| bytesToNat <| Dregg2.Crypto.Blake3.hash (entryTag ++ line)

end Dregg2.Stream.Hash
