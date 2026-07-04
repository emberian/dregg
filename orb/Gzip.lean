import Deflate
/-
# Gzip — the gzip container (RFC 1952) over DEFLATE inflate

`gzip` (RFC 1952) wraps a DEFLATE stream (RFC 1951, modelled in `Deflate.lean`)
in a self-describing container: a fixed magic number and header, the compressed
payload, and an 8-byte trailer carrying a CRC-32 of the *uncompressed* data and
its size mod 2³². A server that accepts `Content-Encoding: gzip` request bodies
parses this container and decompresses — the dangerous direction (a
decompression bomb). This file models `gunzip` (the decompress side) as a total
function over `Deflate.inflate`, and carries three properties:

  * **Header well-formedness** (`gzip_header_wellformed`): a header built by
    `mkHeader` parses back, exposing the RFC 1952 §2.3 magic (`ID1=0x1f`,
    `ID2=0x8b`) and method (`CM=0x08`, DEFLATE).
  * **Integrity checking** (`gzip_crc_checked`): the trailer CRC-32 is verified.
    A stream whose CRC does not match the inflated bytes is *rejected*
    (`crcMismatch`), never accepted — a corrupted or forged payload cannot pass.
  * **The decompression-bomb bound** (`gunzip_output_bounded`): `gunzip` inflates
    under the caller's ceiling, so the output is at most `cfg.maxOut` bytes for
    *every* input. The bound composes directly from `Deflate.inflate_output_bounded`.

The CRC-32 here is the standard gzip/zlib CRC (reflected polynomial `0xEDB88320`),
implemented as a real total function and validated against published vectors
(`crc32 [] = 0`, `crc32 "hi" = 0xD8932AAC`). It is a checksum, not a cryptographic
MAC — it detects accidental corruption, not adversarial tampering (an attacker who
controls the payload can recompute it). The engine's authenticity guarantees live
in `Crypto`/`TlsCrypto`, not here.

The container is modelled as a whole buffer (not streaming): the last 8 bytes are
the trailer, the bytes between the header and the trailer are the DEFLATE payload.
`gunzip` handles the RFC 1952 optional header fields (FEXTRA / FNAME / FCOMMENT /
FHCRC) by skipping them, total on all input.
-/

namespace Gzip

open Deflate

/-! ## CRC-32 (RFC 1952 §8, the reflected `0xEDB88320` variant) -/

/-- One byte's worth of the bit-reflected CRC-32 update: `n` reduction rounds. -/
def crc32Round : Nat → UInt32 → UInt32
  | 0, c => c
  | n + 1, c => crc32Round n (if c &&& 1 == 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1)

/-- Fold one data byte into the running CRC (8 reduction rounds). -/
def crc32Byte (c : UInt32) (b : UInt8) : UInt32 := crc32Round 8 (c ^^^ b.toUInt32)

/-- The gzip CRC-32 of a byte list: pre-conditioned with all-ones, folded, then
inverted. Matches `zlib.crc32` (validated: `crc32 [] = 0`, `crc32 "hi" =
0xD8932AAC`). -/
def crc32 (data : List UInt8) : UInt32 :=
  (data.foldl crc32Byte 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-! ## Little-endian 32-bit fields (RFC 1952 §2.3.1) -/

/-- Encode `n` as 4 little-endian bytes. -/
def u32le (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256),
   UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 16777216 % 256)]

/-- Read a 4-byte little-endian field. -/
def readU32le (bs : List UInt8) : Option (Nat × List UInt8) :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: r =>
    some (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat, r)
  | _ => none

/-! ## The gzip header (RFC 1952 §2.3) -/

/-- The fixed part of a gzip header we retain: magic, method, flags. -/
structure Header where
  id1 : UInt8
  id2 : UInt8
  cm : UInt8
  flg : UInt8
  deriving Repr, DecidableEq

/-- Skip a zero-terminated field (FNAME / FCOMMENT), fuel-bounded. -/
def dropZStr : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs => if b == 0 then some bs else dropZStr fuel bs

/-- Parse a gzip header (RFC 1952 §2.3): the 10 fixed bytes (`ID1 ID2 CM FLG`,
`MTIME`×4, `XFL`, `OS`), then the FLG-selected optional fields (FEXTRA, FNAME,
FCOMMENT, FHCRC). Returns the header and the bytes after it (payload ‖ trailer),
or `none` on a bad magic/method or a truncated optional field. -/
def parseHeader (input : List UInt8) : Option (Header × List UInt8) :=
  match input with
  | id1 :: id2 :: cm :: flg :: _m0 :: _m1 :: _m2 :: _m3 :: _xfl :: _os :: rest0 =>
    if id1 == 0x1f && id2 == 0x8b && cm == 0x08 then
      let step1 : Option (List UInt8) :=
        if flg &&& 0x04 == 0x04 then
          match rest0 with
          | xl0 :: xl1 :: r => some (r.drop (xl0.toNat + 256 * xl1.toNat))
          | _ => none
        else some rest0
      match step1 with
      | none => none
      | some r1 =>
        match (if flg &&& 0x08 == 0x08 then dropZStr (r1.length + 1) r1 else some r1) with
        | none => none
        | some r2 =>
          match (if flg &&& 0x10 == 0x10 then dropZStr (r2.length + 1) r2 else some r2) with
          | none => none
          | some r3 =>
            match (if flg &&& 0x02 == 0x02 then
                     match r3 with | _ :: _ :: r => some r | _ => none
                   else some r3) with
            | none => none
            | some r4 => some (⟨id1, id2, cm, flg⟩, r4)
    else none
  | _ => none

/-! ## gunzip -/

/-- Typed gunzip failures — every one a total outcome. -/
inductive GzErr where
  | badHeader      -- bad magic / method, or truncated header
  | truncated      -- missing trailer / trailer too short
  | inflateError   -- the DEFLATE payload failed to inflate
  | crcMismatch    -- trailer CRC-32 ≠ CRC of the inflated bytes
  | sizeMismatch   -- trailer ISIZE ≠ (inflated size mod 2³²)
  deriving Repr, DecidableEq

/-- gunzip result: the (bounded) output and an optional typed failure. -/
structure Out where
  out : Array UInt8
  err : Option GzErr

/-- **gunzip**: parse the gzip container and decompress under an output ceiling.
The last 8 bytes are the trailer (`CRC32` ‖ `ISIZE`, both little-endian); the
bytes between header and trailer are the DEFLATE payload. On any failure the
output is `#[]` (nothing is handed back); on success it is exactly the inflated
bytes, whose CRC-32 and size have been checked against the trailer. Total, and the
output never exceeds `cfg.maxOut` (`gunzip_output_bounded`). -/
def gunzip (cfg : Cfg) (input : List UInt8) : Out :=
  match parseHeader input with
  | none => ⟨#[], some .badHeader⟩
  | some (_, body) =>
    if body.length < 8 then ⟨#[], some .truncated⟩
    else
      let n := body.length - 8
      let payload := body.take n
      let trailer := body.drop n
      let r := inflate cfg payload
      match r.err with
      | some _ => ⟨#[], some .inflateError⟩
      | none =>
        match readU32le trailer, readU32le (trailer.drop 4) with
        | some (crcStored, _), some (isize, _) =>
          if (crc32 r.out.toList).toNat != crcStored then ⟨#[], some .crcMismatch⟩
          else if r.out.size % 4294967296 != isize then ⟨#[], some .sizeMismatch⟩
          else ⟨r.out, none⟩
        | _, _ => ⟨#[], some .truncated⟩

/-! ## Container builders (for the round-trip and integrity theorems) -/

/-- A minimal gzip header: magic `1f 8b`, method DEFLATE, `FLG=0` (no optional
fields), `MTIME=0`, `XFL=0`, `OS=0xff` (unknown). -/
def mkHeader : List UInt8 := [0x1f, 0x8b, 0x08, 0x00, 0, 0, 0, 0, 0x00, 0xff]

/-- Wrap a byte list as a gzip stream whose payload is a single stored DEFLATE
block: header, `deflateStored x`, then the trailer `CRC32(x) ‖ (|x| mod 2³²)`. -/
def gzipStored (x : List UInt8) : List UInt8 :=
  mkHeader ++ deflateStored x ++ u32le (crc32 x).toNat ++ u32le (x.length % 4294967296)

/-! ## Theorems -/

/-- **Header well-formedness.** A `mkHeader`-built header parses back: the parser
consumes exactly the header and returns the trailing bytes untouched, and the
recovered header carries the RFC 1952 magic (`ID1=0x1f`, `ID2=0x8b`) and method
(`CM=0x08`, DEFLATE). -/
theorem gzip_header_wellformed (rest : List UInt8) :
    parseHeader (mkHeader ++ rest)
      = some (⟨0x1f, 0x8b, 0x08, 0x00⟩, rest)
    ∧ (⟨0x1f, 0x8b, 0x08, 0x00⟩ : Header).id1 = 0x1f
    ∧ (⟨0x1f, 0x8b, 0x08, 0x00⟩ : Header).id2 = 0x8b
    ∧ (⟨0x1f, 0x8b, 0x08, 0x00⟩ : Header).cm = 0x08 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The decompression-bomb bound.** For every ceiling and every input, gunzip's
output is at most `cfg.maxOut` bytes. Composes from `Deflate.inflate_output_bounded`:
the only non-empty output comes from `inflate`, which is itself bounded; every
failure path returns `#[]`. A tiny gzip stream cannot force an unbounded expansion. -/
theorem gunzip_output_bounded (cfg : Cfg) (input : List UInt8) :
    (gunzip cfg input).out.size ≤ cfg.maxOut := by
  unfold gunzip
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · dsimp only
      split
      · exact Nat.zero_le _
      · split
        · split
          · exact Nat.zero_le _
          · split
            · exact Nat.zero_le _
            · exact inflate_output_bounded cfg _
        · exact Nat.zero_le _

set_option maxRecDepth 100000 in
/-- **Integrity: a valid gzip stream is accepted.** For the concrete input `"hi"`,
gunzip of the well-formed `gzipStored` container returns exactly the bytes, with no
error — the header parses, the stored block inflates, and the trailer CRC-32 and
size both match. -/
theorem gzip_accepts_valid :
    (gunzip ⟨100⟩ (gzipStored [0x68, 0x69])).out = #[0x68, 0x69]
      ∧ (gunzip ⟨100⟩ (gzipStored [0x68, 0x69])).err = none := by
  refine ⟨?_, ?_⟩ <;> rfl

set_option maxRecDepth 100000 in
/-- **Integrity: a wrong CRC is rejected (`gzip_crc_checked`).** Take the valid
container for `"hi"` and corrupt its trailer CRC-32 (flip the low byte). gunzip
does not return the bytes; it fails with `crcMismatch`. Concretely: the stored
block still inflates to `[0x68, 0x69]`, but `crc32 [0x68, 0x69] ≠` the tampered
trailer value, so the check fires and nothing is handed back. -/
theorem gzip_crc_checked :
    (gunzip ⟨100⟩
      (mkHeader ++ deflateStored [0x68, 0x69]
        ++ u32le ((crc32 [0x68, 0x69]).toNat ^^^ 0xff)   -- corrupted CRC
        ++ u32le (2 % 4294967296)))
      = ⟨#[], some GzErr.crcMismatch⟩ := by
  rfl

end Gzip
