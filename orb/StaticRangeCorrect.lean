/-
# StaticRangeCorrect — RFC 9110 §14.1.2 byte-range CORRECTNESS by refinement

This upgrades the static-file range handler from SAFETY (a `206` body is *some*
sub-slice, an unsatisfiable range is *some* `416`) to CORRECTNESS: the `206`
body is the octet sequence RFC 9110 §14.1.2 *names*, character for character.

The specification here is written **from the RFC**, independent of the handler:
it says what a byte-range response body SHOULD be, using positional octet
indexing (`octets`) — not the handler's `slice`, not `resolveRange`. The
refinement theorems then prove `StaticFile.serveResolved` (the real handler)
produces exactly the specified response on every input.

RFC 9110 §14.1.2 (Byte Ranges):
  * "A byte-range-spec `first-byte-pos "-" [last-byte-pos]` … the last-byte-pos
    value … If the value is greater than or equal to the current length of the
    representation data, … the last-byte-pos is taken to be … one less than the
    current length." — the `min(b, N-1)` clamp.
  * "A client can request the last N bytes … `suffix-length` … If the
    selected representation is shorter than the specified suffix-length, the
    entire representation is used." — suffix = last `min(k, N)` bytes.
  * "A byte-range-spec is invalid if the last-byte-pos value is present and less
    than the first-byte-pos." and §14.1.2 / §15.5.17: "if the first-byte-pos …
    are greater than … the current length, … the byte-range-spec is
    unsatisfiable" → `416 (Range Not Satisfiable)`.

Independent SPEC:   `spec`  (via `octets`, positional indexing).
Refinement:         `serveResolved_refines_spec` — the handler = the spec.
Non-vacuity:        `octets_rejects_offbyone`, worked §2.1 examples.
-/

import StaticFile

namespace StaticRangeCorrect

open StaticFile (RangeSpec Config Req Resp serveResolved slice resolveRange)

/-- Raw representation octets. -/
abbrev Bytes := List UInt8

/-! ## The independent RFC octet-sequence characterization

The single primitive the specification is built on. `octets body lo hi` is the
sequence `body[lo], body[lo+1], …, body[hi]` — the octets RFC 9110 §14.1.2
selects, given purely by their positions. It refers to nothing in the handler:
no `slice`, no `drop`/`take` framing, only `List.getD` positional access. -/
def octets (body : Bytes) (lo hi : Nat) : Bytes :=
  (List.range (hi + 1 - lo)).map (fun i => body.getD (lo + i) 0)

/-- `octets` has the RFC 9110 §14.1.2 partial length `hi − lo + 1` (for a
well-formed `lo ≤ hi`). -/
theorem octets_length (body : Bytes) (lo hi : Nat) :
    (octets body lo hi).length = hi + 1 - lo := by
  unfold octets
  rw [List.length_map, List.length_range]

/-! ## The RFC-mandated result of a single byte-range -/

/-- The response class RFC 9110 §14.1.2 mandates for a single byte-range on a
representation of length `N = body.length`: a `partial` carrying the exact
selected octets and their inclusive `(first, last)` offsets, or
`unsatisfiable`. This is an outcome value, defined with no reference to how the
handler computes it. -/
inductive RangeResult
  /-- `206 (Partial Content)`: the selected octets and inclusive offsets. -/
  | sub (body : Bytes) (first last : Nat)
  /-- `416 (Range Not Satisfiable)`. -/
  | unsatisfiable
deriving DecidableEq, Repr

/-- **The independent specification.** For each byte-range form, the octets the
handler MUST return (RFC 9110 §14.1.2). Written from the RFC prose:

  * `bytes=a-b` selects octets `a … min(b, N-1)`, provided the spec is
    well-formed (`a ≤ b`) and satisfiable (`a < N`); otherwise `416`.
  * `bytes=a-` selects octets `a … N-1` when `a < N`; otherwise `416`.
  * `bytes=-k` selects the *last* `min(k, N)` octets, i.e. positions
    `N − min(k,N) … N-1`, provided `k > 0` and `N > 0`; otherwise `416`.

Note the offsets and the octet selection are given directly; there is no shared
code with `StaticFile.resolveRange`/`StaticFile.slice`. -/
def spec (body : Bytes) : RangeSpec → RangeResult
  | .fromTo a b =>
      if b < a ∨ a ≥ body.length then .unsatisfiable
      else
        let hi := min b (body.length - 1)
        .sub (octets body a hi) a hi
  | .fromOnly a =>
      if a ≥ body.length then .unsatisfiable
      else .sub (octets body a (body.length - 1)) a (body.length - 1)
  | .suffix k =>
      if k = 0 ∨ body.length = 0 then .unsatisfiable
      else
        let len := min k body.length
        .sub (octets body (body.length - len) (body.length - 1))
                 (body.length - len) (body.length - 1)

/-! ## Bridge lemmas connecting the handler's `slice`/`resolveRange` to the spec -/

/-- **The handler's `slice` computes exactly the specified octets.** This is the
non-trivial content: `StaticFile.slice b s e = (b.drop s).take (e-s+1)` (a
drop/take framing) equals `octets b s e` (positional indexing), whenever the
offsets are well-formed (`s ≤ e`) and in range (`e < length`). -/
theorem slice_eq_octets (b : Bytes) (s e : Nat) (hse : s ≤ e) (he : e < b.length) :
    slice b s e = octets b s e := by
  apply List.ext_getElem?
  intro i
  show ((b.drop s).take (e - s + 1))[i]? = _
  unfold octets
  rw [List.getElem?_take, List.getElem?_drop, List.getElem?_map]
  by_cases hi : i < e + 1 - s
  · rw [List.getElem?_range hi]
    have hcond : i < e - s + 1 := by omega
    rw [if_pos hcond]
    have hlt : s + i < b.length := by omega
    rw [List.getElem?_eq_getElem hlt]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  · have hcond : ¬ i < e - s + 1 := by omega
    rw [if_neg hcond]
    have hnone : (List.range (e + 1 - s))[i]? = none := by
      apply List.getElem?_eq_none
      rw [List.length_range]; omega
    rw [hnone]; rfl

/-- **`resolveRange` agrees with the spec's satisfiable/unsatisfiable decision
and its offsets.** When the spec says `partial _ f l`, the handler's
`resolveRange` yields exactly `some (f, l)`; when the spec says `unsatisfiable`,
`resolveRange` yields `none`. (The bodies are handled by `slice_eq_octets`.) -/
theorem resolveRange_matches (body : Bytes) (rs : RangeSpec) :
    (match spec body rs with
     | .sub _ f l => resolveRange body.length rs = some (f, l)
     | .unsatisfiable => resolveRange body.length rs = none) := by
  cases rs with
  | fromTo a b =>
    by_cases h1 : b < a
    · simp [spec, resolveRange, h1]
    · by_cases h2 : a ≥ body.length
      · simp [spec, resolveRange, h1, h2]
      · simp [spec, resolveRange, h1, h2]
  | fromOnly a =>
    by_cases h2 : a ≥ body.length
    · simp [spec, resolveRange, h2]
    · simp [spec, resolveRange, h2]
  | suffix k =>
    by_cases h1 : k = 0
    · simp [spec, resolveRange, h1]
    · by_cases h2 : body.length = 0
      · simp [spec, resolveRange, h1, h2]
      · by_cases h3 : k ≥ body.length
        · have hm : min k body.length = body.length := by omega
          simp [spec, resolveRange, h1, h2, h3, hm]
        · have hm : min k body.length = k := by omega
          have h3' : ¬ k ≥ body.length := h3
          simp [spec, resolveRange, h1, h2, h3', hm]

/-- Whenever the spec yields a `sub eb f l`, its body `eb` is exactly the
positional octet sequence `octets body f l` at the reported offsets. (Read off
`spec` by cases; no handler involvement.) -/
theorem specBody_octets (body : Bytes) (rs : RangeSpec) (eb : Bytes) (f l : Nat)
    (hs : spec body rs = .sub eb f l) : eb = octets body f l := by
  cases rs with
  | fromTo a b =>
    simp only [spec] at hs
    by_cases hcut : b < a ∨ a ≥ body.length
    · rw [if_pos hcut] at hs; exact absurd hs (by simp)
    · rw [if_neg hcut] at hs
      simp only [RangeResult.sub.injEq] at hs
      obtain ⟨heb, hf, hl⟩ := hs; rw [← hf, ← hl]; exact heb.symm
  | fromOnly a =>
    simp only [spec] at hs
    by_cases hcut : a ≥ body.length
    · rw [if_pos hcut] at hs; exact absurd hs (by simp)
    · rw [if_neg hcut] at hs
      simp only [RangeResult.sub.injEq] at hs
      obtain ⟨heb, hf, hl⟩ := hs; rw [← hf, ← hl]; exact heb.symm
  | suffix k =>
    simp only [spec] at hs
    by_cases hcut : k = 0 ∨ body.length = 0
    · rw [if_pos hcut] at hs; exact absurd hs (by simp)
    · rw [if_neg hcut] at hs
      simp only [RangeResult.sub.injEq] at hs
      obtain ⟨heb, hf, hl⟩ := hs; rw [← hf, ← hl]; exact heb.symm

/-! ## The refinement theorem -/

/-- **`serveResolved_refines_spec` — the handler REFINES the independent spec.**
For a request that reaches the range machinery (a file is present, the
`If-None-Match` precondition does not fire, a single `Range` is asked), the
response `StaticFile.serveResolved` selects is *exactly* the one the spec
mandates:

  * spec `partial eb f l`  ⇒  handler `= partialContent eb f l N etag`
    with body precisely the specified octets `eb`;
  * spec `unsatisfiable`   ⇒  handler `= rangeNotSatisfiable N` (a `416`).

Non-vacuous: `eb` is `octets body …`, an implementation whose slice is off by
one octet produces a *different* `partialContent` body and fails this equality
(see `octets_rejects_offbyone`). -/
theorem serveResolved_refines_spec (cfg : Config) (req : Req) (path : List String)
    (body : Bytes) (rs : RangeSpec)
    (hfile : cfg.fs path = some body)
    (hnm : StaticFile.ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = false)
    (hrange : req.range = some rs) :
    (match spec body rs with
     | .sub eb f l =>
         serveResolved cfg req path = .partialContent eb f l body.length (cfg.etag path)
     | .unsatisfiable =>
         serveResolved cfg req path = .rangeNotSatisfiable body.length) := by
  have hmatch := resolveRange_matches body rs
  -- case on the spec outcome, feeding the resolveRange match through hmatch
  cases hs : spec body rs with
  | unsatisfiable =>
    rw [hs] at hmatch
    simp only [serveResolved, hfile, hnm, hrange, hmatch, Bool.false_eq_true, if_false]
  | sub eb f l =>
    rw [hs] at hmatch
    -- the spec's body eb is octets; it equals slice at the resolved offsets
    have hvalid := StaticFile.resolveRange_valid body.length rs f l hmatch
    have hb : eb = octets body f l := specBody_octets body rs eb f l hs
    have hslice : slice body f l = eb := by
      rw [hb]; exact slice_eq_octets body f l hvalid.1 hvalid.2
    simp only [serveResolved, hfile, hnm, hrange, hmatch, hslice, Bool.false_eq_true, if_false]

/-- **Body corollary.** In the satisfiable case the served `206` body is
literally the specified octet sequence, of the RFC 9110 §14.1.2 partial length
`last − first + 1`. -/
theorem serveResolved_body_exact (cfg : Config) (req : Req) (path : List String)
    (body : Bytes) (rs : RangeSpec) (eb : Bytes) (f l : Nat)
    (hfile : cfg.fs path = some body)
    (hnm : StaticFile.ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = false)
    (hrange : req.range = some rs)
    (hspec : spec body rs = .sub eb f l) :
    (serveResolved cfg req path).body = eb ∧
    (serveResolved cfg req path).status = 206 ∧
    eb.length = l + 1 - f := by
  have href := serveResolved_refines_spec cfg req path body rs hfile hnm hrange
  rw [hspec] at href
  have hR : serveResolved cfg req path
      = Resp.partialContent eb f l body.length (cfg.etag path) := href
  have hb : eb = octets body f l := specBody_octets body rs eb f l hspec
  refine ⟨by simp only [hR, Resp.body], by simp only [hR, Resp.status], ?_⟩
  rw [hb, octets_length]

/-! ## Non-vacuity

The spec is not the handler renamed, and the refinement is not `impl = impl`:
an off-by-one slice is a DIFFERENT value the spec rejects, and the worked
RFC §14.1.2 / §2.1 examples pin concrete octet sequences. -/

/-- **`octets_rejects_offbyone`.** On `[10,11,12,13,14]`, the range `bytes=1-3`
selects exactly `[11,12,13]`. An implementation that dropped the final octet
(`take (e-s)` instead of `take (e-s+1)`) would serve `[11,12]`, and an
implementation that clamped `min b N` instead of `min b (N-1)` would read past
the end. The spec value differs from both — so a wrong impl FAILS the
refinement equality. -/
theorem octets_rejects_offbyone :
    -- the correct selection
    spec [10, 11, 12, 13, 14] (.fromTo 1 3) = .sub [11, 12, 13] 1 3 ∧
    -- an off-by-one (short) body is a different value the spec rejects
    (octets [10, 11, 12, 13, 14] 1 3 ≠ [11, 12]) ∧
    (octets [10, 11, 12, 13, 14] 1 3 ≠ [11, 12, 13, 14]) := by
  decide

/-- RFC 9110 §14.1.2 suffix (general): `bytes=-k` on any representation of
length `N` with `0 < k ≤ N` pins offsets `N−k … N−1` — the LAST `k` octets. On
`N = 10000, k = 500` this is `9500 … 9999`, the RFC's worked value. A handler
that used `N−k+1` or `N` for the first offset would fail this equality. -/
theorem spec_suffix_offsets (body : Bytes) (k : Nat)
    (hk : 0 < k) (hkN : k ≤ body.length) :
    spec body (.suffix k)
      = .sub (octets body (body.length - k) (body.length - 1))
             (body.length - k) (body.length - 1) := by
  have h1 : ¬ (k = 0 ∨ body.length = 0) := by omega
  have h2 : min k body.length = k := by omega
  simp only [spec, if_neg h1, h2]

/-- The §14.1.2 "remainder" clamp is exact (general): `bytes=a-b` with
`a < N ≤ b+1` selects offsets `a … N−1` — the last-byte-pos clamped to the
remainder `N−1`, never `b`. On `a = 500, b = 99999, N = 8000` this is
`500 … 7999`. -/
theorem spec_clamp_offsets (body : Bytes) (a b : Nat)
    (ha : a < body.length) (hb : body.length - 1 ≤ b) :
    spec body (.fromTo a b)
      = .sub (octets body a (body.length - 1)) a (body.length - 1) := by
  have h1 : ¬ (b < a ∨ a ≥ body.length) := by omega
  have h2 : min b (body.length - 1) = body.length - 1 := by omega
  simp only [spec, if_neg h1, h2]

/-- An out-of-range first-byte-pos is unsatisfiable → `416` (RFC 9110 §14.1.2,
§15.5.17): `bytes=a-` with `a ≥ N`. -/
theorem spec_unsatisfiable (body : Bytes) (a : Nat) (ha : a ≥ body.length) :
    spec body (.fromOnly a) = .unsatisfiable := by
  simp only [spec, if_pos ha]

/-- A short suffix uses the whole representation (RFC 9110 §14.1.2: a
suffix-length larger than the representation yields all of it). Concrete
witness: `bytes=-100` on a 3-octet body is all three octets at offsets `0…2`. -/
theorem spec_suffix_whole :
    spec [7, 8, 9] (.suffix 100) = .sub [7, 8, 9] 0 2 := by decide

end StaticRangeCorrect

#print axioms StaticRangeCorrect.serveResolved_refines_spec
#print axioms StaticRangeCorrect.serveResolved_body_exact
#print axioms StaticRangeCorrect.slice_eq_octets
#print axioms StaticRangeCorrect.octets_rejects_offbyone
