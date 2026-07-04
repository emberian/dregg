import Body.ContentLength

/-!
# Correctness of Content-Length body framing (RFC 9112 §6.2, §6.3)

`Body/ContentLength.lean` establishes *safety* facts about the streaming reader —
`feed` preserves `delivered.length ≤ total`, the fold is order-preserving, and the
reader never overshoots. Those say the reader never delivers *more* than the
declared length. They do not, on their own, pin the delivered bytes to the
RFC-mandated ones.

This file upgrades that to a *correctness* claim: the reader's output MATCHES what
the RFC dictates, stated against an independent specification.

## What the RFC mandates

RFC 9112 §6.2 (Content-Length): the field value is a decimal count that "defines
the message body length in octets." §6.3 gives the algorithm that picks the body
length; rule 6 states that when a valid Content-Length of value `N` is present,
"the message body length is equal to `N`," and the recipient reads that exact
count from the connection. The framing consequence, spelled out in §6.3 and in
the connection-management rules of §9.3–§9.5, is a partition of the inbound octet
stream at offset `N`:

* the message body is **exactly the next `N` octets** of the stream, in order;
* **fewer** than `N` octets available is an *incomplete* message — no body has
  been framed yet;
* **more** than `N` octets means the surplus is not part of this body: it is the
  start of the **next message** on the connection (a pipelined request). Reading
  those octets into the body is precisely the request-smuggling defect this
  property forbids.

## The specification (independent of the reader)

`IsFraming N input body rest` is a predicate read straight off the RFC partition:
a split of the inbound stream `input` into a leading `body` and a trailing `rest`
is the Content-Length framing for count `N` exactly when

    body ++ rest = input   ∧   body.length = N

The first conjunct says the two pieces reassemble the stream in order — nothing is
reordered, inserted, or dropped. The second says the body carries the declared
count *exactly*: not fewer (that would be an incomplete message, no valid framing)
and not more (the surplus octets belong to `rest`, the next message).

Crucially this predicate never mentions `Reader`, `feed`, `delivered`,
`remaining`, `take`, or `drop`. It is not the reader renamed: it is a declarative
statement of which `(body, rest)` splits are legal for which count. A reader that
delivered `N ± k` octets, or that mis-parsed the count `N`, would produce a body
whose length is not `N`, which this predicate rejects — see the non-vacuity
theorems at the foot of the file.

## The refinement theorem

`framing_unique` shows the predicate pins down *at most one* split: any two
framings of the same stream for the same count are equal. `feed_isFraming` shows
the reader's actual output — the delivered prefix paired with the untouched tail
`input.drop N` — *is* a framing. Together, `feed_refines_framing` states that the
reader produces THE unique RFC-mandated framing: it is a correct framing, and
every correct framing equals it.
-/

namespace Body
namespace ContentLength

/-- **The specification, from RFC 9112 §6.2/§6.3.** A split of the inbound octet
stream `input` into a leading `body` and a trailing `rest` is the Content-Length
framing for count `n` exactly when the two pieces reassemble the stream in order
(`body ++ rest = input`) and the body carries the declared count exactly
(`body.length = n`). Defined purely over byte lists and the count — no reference
to the `Reader`, its `feed`, or `take`/`drop`. -/
def IsFraming (n : Nat) (input body rest : Bytes) : Prop :=
  body ++ rest = input ∧ body.length = n

/-- A framing can only exist once the stream carries at least `n` octets: fewer
than `n` is an incomplete message with no valid framing. (RFC 9112 §6.3: the body
is not framed until `N` octets have arrived.) -/
theorem framing_requires_complete {n : Nat} {input body rest : Bytes}
    (h : IsFraming n input body rest) : n ≤ input.length := by
  obtain ⟨hcat, hlen⟩ := h
  have : body.length ≤ input.length := by
    rw [← hcat, List.length_append]; omega
  omega

/-- **The framing is unique.** Any two Content-Length framings of the same stream
for the same count agree on both the body and the remainder. The RFC partition at
offset `n` is a function of `(n, input)`, so there is nothing for a correct reader
to choose. -/
theorem framing_unique {n : Nat} {input b₁ r₁ b₂ r₂ : Bytes}
    (h₁ : IsFraming n input b₁ r₁) (h₂ : IsFraming n input b₂ r₂) :
    b₁ = b₂ ∧ r₁ = r₂ := by
  obtain ⟨hc₁, hl₁⟩ := h₁
  obtain ⟨hc₂, hl₂⟩ := h₂
  exact List.append_inj (hc₁.trans hc₂.symm) (hl₁.trans hl₂.symm)

/-- **Existence.** Once the stream carries at least `n` octets, the RFC framing
exists: the length-`n` prefix as body and the remainder as the next message. This
witnesses that the specification is satisfiable (not vacuously empty). -/
theorem framing_exists {n : Nat} {input : Bytes} (h : n ≤ input.length) :
    IsFraming n input (input.take n) (input.drop n) := by
  refine ⟨List.take_append_drop n input, ?_⟩
  rw [List.length_take]; omega

/-- **Soundness / refinement.** On a stream carrying at least `n` octets, the
reader's actual output is a correct RFC framing: the bytes it delivers, paired
with the untouched tail `input.drop n`, satisfy `IsFraming`. This is the bridge
from the concrete `Reader.feed` to the independent specification. -/
theorem feed_isFraming (n : Nat) (input : Bytes) (h : n ≤ input.length) :
    IsFraming n input ((Reader.init n).feed input).delivered (input.drop n) := by
  have hd : ((Reader.init n).feed input).delivered = input.take n := by
    rw [feed_delivered _ _ (init_wf n)]; simp [Reader.init]
  rw [hd]; exact framing_exists h

/-- **The refinement theorem.** On a stream carrying at least `n` octets, the
reader produces THE unique Content-Length framing mandated by RFC 9112 §6.2/§6.3:

* its output `(delivered, input.drop n)` is a correct framing (`IsFraming`), and
* every split satisfying the specification equals the reader's output.

The reader delivers exactly the length-`n` prefix as the body and leaves the
remainder as the next message — no fewer octets (incomplete), no more (smuggled
from the following message). -/
theorem feed_refines_framing (n : Nat) (input : Bytes) (h : n ≤ input.length) :
    IsFraming n input ((Reader.init n).feed input).delivered (input.drop n) ∧
    (∀ b r, IsFraming n input b r →
      b = ((Reader.init n).feed input).delivered ∧ r = input.drop n) := by
  refine ⟨feed_isFraming n input h, ?_⟩
  intro b r hbr
  exact framing_unique hbr (feed_isFraming n input h)

/-- The reader's `complete` flag agrees with the specification's completeness
condition: after feeding the whole stream, the reader reports terminal exactly
when at least `n` octets have arrived — the same threshold at which a framing
exists. -/
theorem complete_iff_framing_exists (n : Nat) (input : Bytes) :
    ((Reader.init n).feed input).complete = true ↔ n ≤ input.length := by
  have hd : ((Reader.init n).feed input).delivered = input.take n := by
    rw [feed_delivered _ _ (init_wf n)]; simp [Reader.init]
  have ht : ((Reader.init n).feed input).total = n := rfl
  simp only [Reader.complete, hd, ht, List.length_take, decide_eq_true_eq]
  omega

/-- **Streaming refinement.** Folding a whole segment stream through a fresh reader
also produces the RFC framing of the concatenated octet stream: on at least `n`
octets, the delivered body paired with the tail satisfies `IsFraming` and is the
unique such split. The framing property is stable across segmentation of the
input. -/
theorem runFeed_refines_framing (n : Nat) (segs : List Bytes)
    (h : n ≤ segs.flatten.length) :
    IsFraming n segs.flatten (runFeed (Reader.init n) segs).delivered
      (segs.flatten.drop n) ∧
    (∀ b r, IsFraming n segs.flatten b r →
      b = (runFeed (Reader.init n) segs).delivered ∧ r = segs.flatten.drop n) := by
  have hd : (runFeed (Reader.init n) segs).delivered = segs.flatten.take n :=
    runFeed_delivered n segs
  have hframe : IsFraming n segs.flatten (runFeed (Reader.init n) segs).delivered
      (segs.flatten.drop n) := by
    rw [hd]; exact framing_exists h
  refine ⟨hframe, ?_⟩
  intro b r hbr
  exact framing_unique hbr hframe

/-! ## Non-vacuity — a wrong reader FAILS the specification

The specification is not the reader renamed, and it is not a tautology: a reader
that delivered the wrong number of octets, or mis-parsed the count, produces a
split the predicate rejects. The following show that concretely.
-/

/-- The predicate is sensitive to the delivered length: any body whose length is
not exactly `n` is rejected, regardless of the remainder. This is the lever the
non-vacuity witnesses below pull. -/
theorem wrong_length_not_framing {n : Nat} {input body rest : Bytes}
    (hlen : body.length ≠ n) : ¬ IsFraming n input body rest := by
  intro h; exact hlen h.2

/-- **Over-reading is rejected (request smuggling).** On a stream strictly longer
than `n`, a reader that delivered the length-`(n+1)` prefix — one octet past the
declared count, pulling the head of the next message into this body — does not
produce a framing, for any claimed remainder. -/
theorem take_more_not_framing {n : Nat} {input : Bytes} (h : n < input.length)
    (rest : Bytes) : ¬ IsFraming n input (input.take (n + 1)) rest := by
  apply wrong_length_not_framing
  rw [List.length_take]; omega

/-- **Under-reading is rejected (truncated body).** On a nonempty declared count
with at least `n` octets available, a reader that delivered only the length-`(n-1)`
prefix — one octet short — does not produce a framing, for any claimed remainder. -/
theorem take_fewer_not_framing {n : Nat} {input : Bytes} (hn : 0 < n)
    (hlen : n ≤ input.length) (rest : Bytes) :
    ¬ IsFraming n input (input.take (n - 1)) rest := by
  apply wrong_length_not_framing
  rw [List.length_take]; omega

/-- **A mis-parsed count is rejected.** A reader that read a count `m ≠ n` and
delivered `m` octets (available on a stream at least `max m n` long) produces a
body of length `m`, which is not a framing for the true count `n`. -/
theorem wrong_total_not_framing {n m : Nat} {input : Bytes} (hne : m ≠ n)
    (hlen : m ≤ input.length) (rest : Bytes) :
    ¬ IsFraming n input (input.take m) rest := by
  apply wrong_length_not_framing
  rw [List.length_take]; omega

/-! ### A fully concrete witness

With `n = 3` and the five-octet stream `[1,2,3,4,5]`, the correct framing is
`([1,2,3], [4,5])`; the over-read `[1,2,3,4]` and the under-read `[1,2]` both fail.
Everything here is closed by kernel computation. -/

/-- The correct three-octet framing of `[1,2,3,4,5]` holds. -/
example : IsFraming 3 [1,2,3,4,5] [1,2,3] [4,5] := by unfold IsFraming; decide

/-- The over-read (four octets — one from the next message) is not a framing. -/
example : ¬ IsFraming 3 [1,2,3,4,5] [1,2,3,4] [5] := by unfold IsFraming; decide

/-- The under-read (two octets — a truncated body) is not a framing. -/
example : ¬ IsFraming 3 [1,2,3,4,5] [1,2] [3,4,5] := by unfold IsFraming; decide

/-- The real reader, fed `[1,2,3,4,5]` with count `3`, delivers exactly `[1,2,3]`
and leaves `[4,5]` — matching the correct framing above, not the wrong ones. -/
example : ((Reader.init 3).feed [1,2,3,4,5]).delivered = [1,2,3] := by decide

end ContentLength
end Body
