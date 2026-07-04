import Dns.Name

/-!
# Correctness of DNS name decoding with compression (RFC 1035 §4.1.4)

`Dns/Name.lean` establishes *safety* facts about `decodeName` — it is total on
every input (adversarial pointer loops included), a decoded name is at most 255
octets, every label is `1..63` octets, and a successful decode advances the
record cursor. Those say the decoder never diverges and never runs off the
buffer. They do **not** say it returns the *right* labels.

This file upgrades that to a *correctness* claim: the decoder's output MATCHES
what RFC 1035 §4.1.4 dictates.

## What RFC 1035 §4.1.4 says

> In this scheme, an entire domain name or a list of labels at the end of a
> domain name is replaced with a pointer to a **prior** occurrence of the same
> name.
>
> The pointer takes the form of a two octet sequence:
>
>     + + + + + + + + + + + + + + + +
>     | 1  1|                OFFSET   |
>     + + + + + + + + + + + + + + + +
>
> The OFFSET field specifies an offset from the start of the message (i.e., the
> first octet of the ID field in the domain header). A zero offset specifies the
> first byte of the ID field, etc.
>
> The compression scheme allows a domain name in a message to be represented as
> either:
>   - a sequence of labels ending in a zero octet
>   - a pointer
>   - a sequence of labels ending with a pointer

So, reading the message as an array of octets, decoding a name at offset `i`
means: inspect octet `msg[i]`.

* If its top two bits are `00`, it is a normal length octet: the low six bits
  give a length `L` (and `L = 0` is the root octet that ends the name). A
  nonzero `L` is followed by `L` label octets `msg[i+1 .. i+L]`, and the rest of
  the name is decoded from offset `i + 1 + L`.
* If its top two bits are `11`, it is a pointer: the low 14 bits (this octet's
  low six bits, times 256, plus the next octet) give an OFFSET, and the name
  continues by decoding from that offset.

The decoded name is the label sequence produced by following that procedure,
with pointers transparently redirecting the read.

## The independent specification

`DecodesTo msg i labels` below is that procedure written as an inductive
relation, *directly from the three bullet points of §4.1.4*. It mentions
neither `readRun`, `followChain`, fuel, nor the implementation's conservative
"strictly backward" pointer guard. It is the declarative meaning of a wire name:

* `root`   — an octet whose value is `0` ends the name (empty label list).
* `label`  — a `00`-tagged nonzero octet contributes the following `L` bytes as
             a label, then the name continues past those bytes.
* `pointer`— an `11`-tagged octet redirects the read to the OFFSET and the name
             is whatever decodes there.

Because it is an *inductive* relation, `DecodesTo msg i labels` holds exactly
when the redirection procedure has a finite derivation. An adversarial pointer
loop yields no finite derivation, so no label list is related to it — the
declarative name is simply undefined there, which is the correct meaning of a
message that does not encode a finite name.

## The refinement theorem

`decodeName_refines_spec` : whenever the implementation accepts a name and
returns labels `d.labels`, those labels satisfy the RFC relation
`DecodesTo msg start d.labels`. The implementation only ever emits genuinely
correct decodes.

Since `DecodesTo` is deterministic (`decodesTo_unique`), this is sharp: the RFC
assigns *at most one* label list to each offset, so the theorem pins the
implementation to THE correct answer. Any implementation that ignored a pointer,
or mis-sliced a label, would return a different list and thereby violate the
theorem (`spec_rejects_pointer_ignoring` exhibits exactly such a wrong answer
being rejected by the spec on a compressed name the real decoder gets right).
-/

namespace DnsNameCorrect

open Dns

/-- **RFC 1035 §4.1.4 name-decode relation.** `DecodesTo msg i labels` holds
when, reading `msg` as octets and starting at offset `i`, the compression
procedure of §4.1.4 produces exactly the label sequence `labels`. Defined purely
from the RFC: no reference to the decoder, its fuel, or its backward-pointer
guard. -/
inductive DecodesTo (msg : Bytes) : Nat → List (List UInt8) → Prop where
  /-- A zero octet is the root label; it ends the name. -/
  | root {i : Nat} (b : UInt8) (hb : msg[i]? = some b) (hz : b.toNat = 0) :
      DecodesTo msg i []
  /-- A `00`-tagged nonzero octet of value `L` contributes the `L` following
  octets as a label, and the name continues from `i + 1 + L`. -/
  | label {i : Nat} {rest : List (List UInt8)} (b : UInt8)
      (hb : msg[i]? = some b) (h00 : b.toNat / 64 = 0) (hpos : b.toNat ≠ 0)
      (hfit : i + 1 + b.toNat ≤ msg.length)
      (hrest : DecodesTo msg (i + 1 + b.toNat) rest) :
      DecodesTo msg i (labelAt msg i b.toNat :: rest)
  /-- An `11`-tagged octet is a pointer to `OFFSET = (b & 0x3f)·256 + b2`; the
  name is whatever decodes at that offset. -/
  | pointer {i target : Nat} {labels : List (List UInt8)} (b b2 : UInt8)
      (hb : msg[i]? = some b) (h11 : b.toNat / 64 = 3)
      (hb2 : msg[i + 1]? = some b2)
      (htarget : target = (b.toNat % 64) * 256 + b2.toNat)
      (hfollow : DecodesTo msg target labels) :
      DecodesTo msg i labels

/-! ## Soundness of the forward reader

`readRun` reads a forward run of labels into `acc`. We show the *new* labels it
appends are exactly a `DecodesTo`-suffix: on `complete`, the suffix is a whole
sub-name (ends at a root octet); on `jump`, the suffix is a prefix that, when
continued from the pointer target, forms a `DecodesTo` name. -/

/-- The reader's output relates to the RFC relation. On `complete` the new
labels form a self-contained decode from `i`; on `jump` they form a prefix whose
continuation from the pointer target completes a decode from `i`. -/
theorem readRun_sound (msg : Bytes) (i : Nat) (acc : List (List UInt8))
    (fuel : Nat) :
    (∀ o e, readRun msg i acc fuel = .complete o e →
        ∃ suf, o = acc ++ suf ∧ DecodesTo msg i suf) ∧
    (∀ t o e, readRun msg i acc fuel = .jump t o e →
        ∃ suf, o = acc ++ suf ∧
          ∀ tail, DecodesTo msg t tail → DecodesTo msg i (suf ++ tail)) := by
  induction fuel generalizing i acc with
  | zero => constructor <;> intro <;> simp [readRun] at *
  | succ fuel ih =>
    constructor
    · -- complete case
      intro o e h
      unfold readRun at h
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        split at h
        · rename_i hzero
          split at h
          · -- root octet
            rename_i hzb
            injection h with ho he; subst ho
            refine ⟨[], by simp, ?_⟩
            exact DecodesTo.root b hb hzb
          · -- nonzero 00 label
            split at h
            · rename_i hfit
              split at h
              · -- recurse
                obtain ⟨suf, hsuf, hdec⟩ :=
                  (ih (i + 1 + b.toNat) (acc ++ [labelAt msg i b.toNat])).1 o e h
                refine ⟨labelAt msg i b.toNat :: suf, ?_, ?_⟩
                · rw [hsuf]; simp
                · exact DecodesTo.label b hb hzero
                    (by omega) hfit hdec
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · rename_i hptr
            split at h
            · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
    · -- jump case
      intro t o e h
      unfold readRun at h
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        split at h
        · rename_i hzero
          split at h
          · exact absurd h (by simp)
          · split at h
            · rename_i hfit
              split at h
              · -- recurse
                obtain ⟨suf, hsuf, hcont⟩ :=
                  (ih (i + 1 + b.toNat) (acc ++ [labelAt msg i b.toNat])).2 t o e h
                refine ⟨labelAt msg i b.toNat :: suf, ?_, ?_⟩
                · rw [hsuf]; simp
                · intro tail htail
                  have := hcont tail htail
                  exact DecodesTo.label b hb hzero (by omega) hfit this
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · rename_i hptr
            split at h
            · exact absurd h (by simp)
            · rename_i b2 hb2
              injection h with ht ho he
              subst ht; subst ho
              refine ⟨[], by simp, ?_⟩
              intro tail htail
              exact DecodesTo.pointer b b2 hb (by omega) hb2 rfl htail
          · exact absurd h (by simp)

/-! ## Soundness of pointer-chain following -/

/-- `followChain` produces a `DecodesTo`-suffix: the labels it appends past `acc`
form a complete decode from `start`. Proved by well-founded recursion on `start`,
matching `followChain`'s own termination measure. -/
theorem followChain_sound (msg : Bytes) (start : Nat) (acc : List (List UInt8)) :
    ∀ final, followChain msg start acc = .okName final →
      ∃ suf, final = acc ++ suf ∧ DecodesTo msg start suf := by
  induction start using Nat.strongRecOn generalizing acc with
  | ind start ih =>
    intro final h
    rw [followChain] at h
    split at h
    · exact absurd h (by simp)
    · -- complete
      rename_i o e heq
      injection h with h; subst h
      exact (readRun_sound msg start acc (msg.length + 1)).1 o e heq
    · -- jump
      rename_i t o e heq
      split at h
      · rename_i hlt
        obtain ⟨suf', hfin, hdec'⟩ := ih t hlt o final h
        obtain ⟨suf0, ho, hcont⟩ :=
          (readRun_sound msg start acc (msg.length + 1)).2 t o e heq
        refine ⟨suf0 ++ suf', ?_, ?_⟩
        · rw [hfin, ho]; simp
        · exact hcont suf' hdec'
      · exact absurd h (by simp)

/-! ## The refinement theorem -/

/-- **Refinement / soundness.** Every name the implementation accepts is a
correct RFC 1035 §4.1.4 decode: if `decodeName msg start = .ok d` then the
declarative relation `DecodesTo msg start d.labels` holds. -/
theorem decodeName_refines_spec (msg : Bytes) (start : Nat) (d : Decoded)
    (h : decodeName msg start = .ok d) : DecodesTo msg start d.labels := by
  unfold decodeName at h
  split at h
  · exact absurd h (by simp)
  · -- forward run completed with no pointer
    rename_i o e heq
    injection h with h; subst h
    obtain ⟨suf, ho, hdec⟩ := (readRun_sound msg start [] (msg.length + 1)).1 o e heq
    simp only [List.nil_append] at ho
    dsimp only [Decoded.labels]; rw [ho]; exact hdec
  · -- forward run hit a pointer, chain followed
    rename_i t o e heq
    split at h
    · rename_i final hfc
      injection h with h; subst h
      obtain ⟨suf0, ho, hcont⟩ :=
        (readRun_sound msg start [] (msg.length + 1)).2 t o e heq
      obtain ⟨suf', hfin, hdec'⟩ := followChain_sound msg t o final hfc
      simp only [List.nil_append] at ho
      subst ho
      dsimp only [Decoded.labels]
      rw [hfin]
      exact hcont suf' hdec'
    · exact absurd h (by simp)

/-! ## Determinism of the specification

The RFC relation is a partial function: at most one label list decodes at each
offset. This makes the refinement theorem sharp — the implementation is pinned
to THE unique correct answer. -/

/-- **The spec is deterministic.** At a given offset a message encodes at most
one name. -/
theorem decodesTo_unique (msg : Bytes) (i : Nat) (l1 : List (List UInt8))
    (h1 : DecodesTo msg i l1) :
    ∀ l2, DecodesTo msg i l2 → l1 = l2 := by
  induction h1 with
  | root b hb hz =>
    intro l2 h2
    cases h2 with
    | root b' hb' hz' => rfl
    | label b' hb' h00' hpos' hfit' hrest' =>
      rw [hb] at hb'; injection hb' with hbb; subst hbb; omega
    | pointer b' b2' hb' h11' hb2' htgt' hfol' =>
      rw [hb] at hb'; injection hb' with hbb; subst hbb; omega
  | label b hb h00 hpos hfit hrest ih =>
    intro l2 h2
    cases h2 with
    | root b' hb' hz' =>
      rw [hb] at hb'; injection hb' with hbb; subst hbb; omega
    | label b' hb' h00' hpos' hfit' hrest' =>
      rw [hb] at hb'; injection hb' with hbb; subst hbb
      rw [ih _ hrest']
    | pointer b' b2' hb' h11' hb2' htgt' hfol' =>
      rw [hb] at hb'; injection hb' with hbb; subst hbb; omega
  | pointer b b2 hb h11 hb2 htarget hfollow ih =>
    intro l2 h2
    cases h2 with
    | root b' hb' hz' =>
      rw [hb] at hb'; injection hb' with hbb; subst hbb; omega
    | label b' hb' h00' hpos' hfit' hrest' =>
      rw [hb] at hb'; injection hb' with hbb; subst hbb; omega
    | pointer b' b2' hb' h11' hb2' htgt' hfol' =>
      rw [hb] at hb'; injection hb' with hbb; subst hbb
      rw [hb2] at hb2'; injection hb2' with hbb2; subst hbb2
      subst htarget; subst htgt'
      exact ih _ hfol'

/-! ## Non-vacuity

We exhibit (1) a real compressed name the decoder accepts, whose labels satisfy
the spec — so the theorem has content on a genuinely pointer-following input; and
(2) a *wrong* answer (the labels a pointer-ignoring decoder would emit) that the
spec REJECTS on that same input — so a broken decoder cannot satisfy the
theorem. -/

/-- The compressed wire message used for the witnesses: `example.com` root-
terminated at offset 0, then `www` + a pointer back to offset 0, starting at
offset 13. This is the RFC's own "shared suffix" compression. -/
def wire : Bytes :=
  [7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
   3, 119, 119, 119, 0xC0, 0x00]

/-- The correct decode of `wire` at offset 13 is `www.example.com`. -/
def correctLabels : List (List UInt8) :=
  [[119, 119, 119], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]

/-- The implementation accepts the compressed name and returns the full labels
(following the backward pointer), consuming 6 octets in the record. -/
theorem impl_accepts_compressed :
    decodeName wire 13 = .ok ⟨correctLabels, 6⟩ := by
  have hr13 : readRun wire 13 [] ((wire : Bytes).length + 1)
      = .jump 0 [[119, 119, 119]] 19 := by decide
  have hr0 : readRun wire 0 [[119, 119, 119]] ((wire : Bytes).length + 1)
      = .complete correctLabels 13 := by decide
  have hfc : followChain wire 0 [[119, 119, 119]] = .okName correctLabels :=
    followChain_complete _ 0 _ _ 13 hr0
  unfold decodeName
  rw [hr13]; simp only [hfc]

/-- The spec agrees: `correctLabels` is the RFC decode of `wire` at offset 13.
Built by hand from the three §4.1.4 constructors — a real derivation that reads
`www`, follows the backward pointer at offset 17 to offset 0, then reads
`example`, `com`, and the root octet. -/
theorem spec_holds_compressed : DecodesTo wire 13 correctLabels := by
  unfold correctLabels
  -- offset 13: label `www` (b = 3), continue at 17
  refine DecodesTo.label (3 : UInt8) (by decide) (by decide) (by decide)
    (by decide) ?_
  -- offset 17: pointer 0xC0 0x00 → target 0
  refine DecodesTo.pointer (0xC0 : UInt8) (0x00 : UInt8) (by decide) (by decide)
    (by decide) rfl ?_
  -- offset 0: label `example` (b = 7), continue at 8
  refine DecodesTo.label (7 : UInt8) (by decide) (by decide) (by decide)
    (by decide) ?_
  -- offset 8: label `com` (b = 3), continue at 12
  refine DecodesTo.label (3 : UInt8) (by decide) (by decide) (by decide)
    (by decide) ?_
  -- offset 12: root octet 0 ends the name
  exact DecodesTo.root (0 : UInt8) (by decide) (by decide)

/-- **Non-vacuity: the spec rejects a pointer-ignoring decode.** The labels a
decoder would emit if it treated the compression pointer at offset 17 as a
terminator — just `[www]` — do NOT satisfy the RFC relation at offset 13. So the
refinement theorem is not vacuously true: a decoder that dropped the pointer
would return `[[119,119,119]]`, which `decodeName_refines_spec` would then
require to satisfy `DecodesTo wire 13`, and it does not. Proved via determinism:
the unique spec decode is the full `correctLabels`. -/
theorem spec_rejects_pointer_ignoring :
    ¬ DecodesTo wire 13 [[119, 119, 119]] := by
  intro h
  have huniq := decodesTo_unique wire 13 correctLabels spec_holds_compressed
    [[119, 119, 119]] h
  exact absurd huniq (by unfold correctLabels; decide)

/-- **Non-vacuity: the spec rejects a mis-sliced label.** A decoder that read one
octet too few for the first label (emitting `ww` instead of `www`) produces a
decode the spec does not accept. -/
theorem spec_rejects_short_label :
    ¬ DecodesTo wire 13 [[119, 119], [101, 120, 97, 109, 112, 108, 101],
        [99, 111, 109]] := by
  intro h
  have huniq := decodesTo_unique wire 13 correctLabels spec_holds_compressed _ h
  exact absurd huniq (by unfold correctLabels; decide)

/-- Putting it together: on a genuinely compressed name, the implementation's
answer satisfies the spec, while the two natural *wrong* answers do not. The
refinement theorem therefore has real discriminating content. -/
theorem impl_answer_is_spec_correct :
    (∃ d, decodeName wire 13 = .ok d ∧ DecodesTo wire 13 d.labels)
    ∧ ¬ DecodesTo wire 13 [[119, 119, 119]] := by
  refine ⟨⟨⟨correctLabels, 6⟩, impl_accepts_compressed, ?_⟩,
    spec_rejects_pointer_ignoring⟩
  exact decodeName_refines_spec wire 13 _ impl_accepts_compressed

end DnsNameCorrect

#print axioms DnsNameCorrect.decodeName_refines_spec
#print axioms DnsNameCorrect.decodesTo_unique
#print axioms DnsNameCorrect.spec_holds_compressed
#print axioms DnsNameCorrect.spec_rejects_pointer_ignoring
