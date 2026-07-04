/-
# StaticFile — serving a file from a document root (RFC 9110/9112, 7232, 7233)

A sans-IO model of the static-file handler: given a request target and a
configured document root, decide the HTTP response. It captures the whole
static surface a file server owes:

  * **Path resolution** composed with the existing traversal discipline
    (`Safety.Traversal.serveStatic` / `Route.Path`): a served path never
    escapes the document root (RFC 9110 §4.1 target normalization + the
    RFC 3986 §5.2.4 dot-segment walk, decoded exactly once).
  * **try_files ordered chain** (a common server idiom, not itself an RFC):
    an ordered list of candidates, the first existing one wins.
  * **SPA fallback**: an unmatched target resolves to the single-page
    application index instead of 404.
  * **Conditional requests** (RFC 7232 §2.3.2, §3.2): an `If-None-Match`
    entity-tag list is compared to the current entity-tag with the WEAK
    comparison function; a hit yields `304 (Not Modified)` with NO body,
    not `200`.
  * **Range requests** (RFC 7233 §2.1, §4.1, §4.4): a satisfiable byte
    range yields `206 (Partial Content)` whose body is exactly the byte
    sub-slice `bytes[start .. end]` (length `end-start+1`); an
    unsatisfiable/invalid range yields `416 (Range Not Satisfiable)`.
  * **Directory autoindex**: a request that resolves to a directory (no
    regular file) yields a listing.

Everything filesystem-shaped enters as uninterpreted total fields of
`Config` — `fs` (path → optional file bytes), `isDir`, `readDir`, `etag`
(the representation's entity-tag). This is the boundary: the theorems are
about the response-selection state, not about any real disk. The crypto/
hash content of an ETag never needs to be interpreted; only its equality
under weak comparison matters, and that is `DecidableEq` on the opaque tag.

Theorems:
  * `static_no_escape`      — the resolved path keeps the document root as
                              a prefix, even under a `..`-popping filesystem
                              walker (reuses `Safety.Traversal`).
  * `conditional_304`       — a matching `If-None-Match` yields `304` with an
                              empty body (status 304, `.body = []`).
  * `range_exact`           — a `206` body is exactly `bytes[start..end]`,
                              with length `end-start+1`.
  * `range_unsatisfiable`   — an unsatisfiable range yields `416`.
  * `try_files_first`       — `tryFiles` serves the first existing candidate.
  * `spa_fallback_unmatched`/`spa_serves_existing` — SPA routing.
  * `autoindex_only_dir`    — a listing is produced only for a directory.

Now discharged (were boundary in the first pass), in `serveConditional`:
  * Multipart/byte-range-set (RFC 7233 §4.1 `multipart/byteranges`):
    `resolveAll`/`mkParts` build one part per satisfiable spec;
    `multipart_ranges_exact` proves each part is its exact slice with the
    §4.1 partial length; `serveConditional_multipart`/`_single` route a
    set to `multipart`/single-`206`/`416` by satisfiable count.
  * `If-Range` weak-validator eligibility (RFC 7233 §3.2): `ifRangeEligible`
    honors a range only on a STRONG entity-tag match or an equal
    `Last-Modified` date; `if_range_weak_full` proves a weak tag falls back
    to a full `200`, `ifRange_date_eligible`/`ifRange_strong_eligible` the
    positive cases.
  * `Last-Modified`/`If-Modified-Since` (RFC 7232 §2.2, §3.3):
    `ifModifiedSince304` + `if_modified_since_304` give the `304` on
    not-modified (ordered after `If-None-Match` per RFC 7232 §6).

Left as a boundary / UNCLOSED:
  * `fs`, `isDir`, `readDir`, `etag`, `lastModified` are uninterpreted — the
    model does not read a real filesystem, and does not claim `fs`/`isDir`
    are mutually exclusive (an implementation must guarantee that separately).
  * The `multipart/byteranges` MIME framing (boundary strings, per-part
    `Content-Range`/`Content-Type` headers) is a serialization-boundary
    detail; the model keeps the parts structured and proves them exact.
-/

import Safety.Traversal

namespace StaticFile

/-- Raw file bytes, modeled as a list for ease of reasoning. -/
abbrev Bytes := List UInt8

/-! ## Entity-tags and the weak comparison function (RFC 7232 §2.3, §2.3.2) -/

/-- An entity-tag: an opaque validator, optionally flagged weak (`W/`).
The opaque payload is modeled as a `String`; only its equality matters. -/
structure ETag where
  weak : Bool
  tag : String
deriving DecidableEq, Repr

/-- **Weak comparison** (RFC 7232 §2.3.2): two entity-tags are equivalent
iff their opaque tags match character-for-character, regardless of either
or both being flagged weak. This is the function a recipient MUST use for
`If-None-Match` (RFC 7232 §3.2). -/
def ETag.weakMatch (a b : ETag) : Bool := a.tag == b.tag

/-- `If-None-Match` evaluates false (i.e. the precondition fails and a `304`
is owed) iff one of the listed tags weak-matches the current entity-tag
(RFC 7232 §3.2). An absent header is the empty list, which never hits. -/
def ifNoneMatchHit (tags : List ETag) (cur : ETag) : Bool :=
  tags.any (fun t => t.weakMatch cur)

/-- **Strong comparison** (RFC 7232 §2.3.2): two entity-tags match strongly iff
NEITHER is flagged weak and their opaque tags are equal. This is the comparison
`If-Range` (RFC 7233 §3.2) requires: a weak validator is never usable to gate a
range, precisely because a weak tag admits semantically-equivalent-but-different
representations. -/
def ETag.strongMatch (a b : ETag) : Bool := !a.weak && !b.weak && a.tag == b.tag

/-! ## Byte ranges (RFC 7233 §2.1) -/

/-- A single byte-range-spec (RFC 7233 §2.1). `fromTo a b` is `bytes=a-b`;
`fromOnly a` is `bytes=a-` (to end); `suffix n` is `bytes=-n` (last `n`). -/
inductive RangeSpec where
  | fromTo (first last : Nat)
  | fromOnly (first : Nat)
  | suffix (suffixLen : Nat)
deriving DecidableEq, Repr

/-- The `If-Range` validator (RFC 7233 §3.2): either an entity-tag or an
HTTP-date. Present when the client wants "give me the range only if the
representation is unchanged; otherwise the whole thing". -/
inductive IfRange where
  | etag (t : ETag)
  | date (d : Nat)
deriving DecidableEq, Repr

/-- Resolve a range against a representation of length `L` into an
inclusive `(start, end)` octet pair, or `none` when invalid/unsatisfiable
(RFC 7233 §2.1, §4.4):

  * `fromTo first last` — invalid if `last < first`; unsatisfiable if
    `first ≥ L`; otherwise `last` is clamped to `L-1` (the "remainder"
    rule when `last ≥ L`).
  * `fromOnly first` — unsatisfiable if `first ≥ L`; else `first .. L-1`.
  * `suffix n` — unsatisfiable if `n = 0` or `L = 0`; if `n ≥ L` the whole
    representation is used (`0 .. L-1`); else `L-n .. L-1`.
-/
def resolveRange (L : Nat) : RangeSpec → Option (Nat × Nat)
  | .fromTo first last =>
      if last < first then none
      else if first ≥ L then none
      else some (first, min last (L - 1))
  | .fromOnly first =>
      if first ≥ L then none else some (first, L - 1)
  | .suffix n =>
      if n = 0 then none
      else if L = 0 then none
      else if n ≥ L then some (0, L - 1) else some (L - n, L - 1)

/-- **A resolved range is well-formed against the representation.** Whenever
`resolveRange L spec` succeeds it yields `start ≤ end < L`. -/
theorem resolveRange_valid (L : Nat) (spec : RangeSpec) (s e : Nat)
    (h : resolveRange L spec = some (s, e)) : s ≤ e ∧ e < L := by
  cases spec with
  | fromTo first last =>
    simp only [resolveRange] at h
    by_cases h1 : last < first
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : first ≥ L
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, he⟩ := h
        subst hs; subst he; omega
  | fromOnly first =>
    simp only [resolveRange] at h
    by_cases h1 : first ≥ L
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, he⟩ := h
      subst hs; subst he; omega
  | suffix n =>
    simp only [resolveRange] at h
    by_cases h1 : n = 0
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : L = 0
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        by_cases h3 : n ≥ L
        · rw [if_pos h3] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hs, he⟩ := h; subst hs; subst he; omega
        · rw [if_neg h3] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hs, he⟩ := h; subst hs; subst he; omega

/-- The exact byte sub-slice `bytes[start .. end]` (inclusive) — the body a
`206` response carries. -/
def slice (b : Bytes) (s e : Nat) : Bytes := (b.drop s).take (e - s + 1)

/-- The slice length is exactly `end - start + 1` whenever `start ≤ end` and
`end` is in range — the RFC 7233 §4.1 partial-content length. -/
theorem slice_length (b : Bytes) (s e : Nat) (hse : s ≤ e) (he : e < b.length) :
    (slice b s e).length = e - s + 1 := by
  unfold slice
  rw [List.length_take, List.length_drop]
  omega

/-! ## The response -/

/-- The HTTP response a static-file handler selects. -/
inductive Resp where
  /-- `200 OK`, full representation. -/
  | ok (body : Bytes) (etag : ETag)
  /-- `206 Partial Content`: the sub-slice, its inclusive `(first,last)`
  offsets and the complete length (the RFC 7233 §4.2 Content-Range data). -/
  | partialContent (body : Bytes) (first last complete : Nat) (etag : ETag)
  /-- `206 Partial Content`, `multipart/byteranges` (RFC 7233 §4.1): one part
  per satisfiable range, each carrying its exact sub-slice and inclusive
  `(first,last)` offsets, plus the complete representation length. -/
  | multipartRanges (parts : List (Bytes × Nat × Nat)) (complete : Nat) (etag : ETag)
  /-- `304 Not Modified`: NO body (RFC 7232 §3.2 / §4.1). -/
  | notModified (etag : ETag)
  /-- `416 Range Not Satisfiable`, carrying the complete length. -/
  | rangeNotSatisfiable (complete : Nat)
  /-- `404 Not Found`. -/
  | notFound
  /-- `200 OK` directory autoindex listing. -/
  | autoindex (entries : List String)
deriving Repr

/-- The numeric status line. -/
def Resp.status : Resp → Nat
  | .ok _ _ => 200
  | .partialContent _ _ _ _ _ => 206
  | .multipartRanges _ _ _ => 206
  | .notModified _ => 304
  | .rangeNotSatisfiable _ => 416
  | .notFound => 404
  | .autoindex _ => 200

/-- The response body. A `304` and a `416` carry none. The `multipart/byteranges`
body is the concatenation of the parts' sub-slices (the MIME boundary framing is
a serialization-boundary detail, not modeled). -/
def Resp.body : Resp → Bytes
  | .ok b _ => b
  | .partialContent b _ _ _ _ => b
  | .multipartRanges parts _ _ => (parts.map (·.1)).flatten
  | .notModified _ => []
  | .rangeNotSatisfiable _ => []
  | .notFound => []
  | .autoindex _ => []

/-! ## Configuration (the filesystem boundary) -/

/-- Static configuration. Every field is an uninterpreted total function —
the filesystem boundary. Theorems hold uniformly over every behavior. -/
structure Config where
  /-- The configured document root, as clean directory segments. -/
  docRoot : List String
  /-- Regular-file contents at a resolved path (`none` = not a regular
  file). -/
  fs : List String → Option Bytes
  /-- Whether a resolved path denotes a directory. -/
  isDir : List String → Bool
  /-- Directory listing (entry names). -/
  readDir : List String → List String
  /-- The current entity-tag of the representation at a path. -/
  etag : List String → ETag
  /-- The representation's `Last-Modified` time (RFC 7232 §2.2), as a
  NumericDate/epoch second. The boundary supplies it; the model only compares. -/
  lastModified : List String → Nat

/-- A request the handler dispatches on. -/
structure Req where
  /-- Raw request-target segments (percent-encoded, possibly adversarial). -/
  target : List String
  /-- The `If-None-Match` entity-tag list (empty if the header is absent). -/
  ifNoneMatch : List ETag := []
  /-- The `Range` byte-range-spec, if a satisfiable single range was asked. -/
  range : Option RangeSpec := none
  /-- `If-Modified-Since` date (RFC 7232 §3.3), if present. -/
  ifModifiedSince : Option Nat := none
  /-- `If-Range` validator (RFC 7233 §3.2), if present. -/
  ifRange : Option IfRange := none
  /-- The full `Range` byte-range-set (RFC 7233 §2.1): possibly several specs,
  yielding a `multipart/byteranges` response when more than one is satisfiable.
  Empty means no `Range` header on this multi-range path. -/
  rangeSet : List RangeSpec := []

/-- **Path resolution**, delegated to the traversal discipline: decode the
target once, remove dot-segments, join under the document root. -/
def resolvePath (cfg : Config) (req : Req) : List String :=
  Safety.Traversal.serveStatic cfg.docRoot req.target

/-! ## Response selection -/

/-- Select the response for a request already resolved to `path`. The order
is exactly RFC 7232 §3.2 + RFC 7233 §3.1: evaluate the precondition FIRST
(a `304` pre-empts everything), then the range, then the full body; a
missing file falls to a directory listing or `404`. -/
def serveResolved (cfg : Config) (req : Req) (path : List String) : Resp :=
  match cfg.fs path with
  | none => if cfg.isDir path then .autoindex (cfg.readDir path) else .notFound
  | some body =>
    if ifNoneMatchHit req.ifNoneMatch (cfg.etag path) then
      .notModified (cfg.etag path)
    else
      match req.range with
      | none => .ok body (cfg.etag path)
      | some spec =>
        match resolveRange body.length spec with
        | none => .rangeNotSatisfiable body.length
        | some (s, e) =>
          .partialContent (slice body s e) s e body.length (cfg.etag path)

/-- The full handler: resolve the path, then select the response. -/
def serve (cfg : Config) (req : Req) : Resp :=
  serveResolved cfg req (resolvePath cfg req)

/-! ## Traversal safety (RFC 9110 §4.1, via `Safety.Traversal`) -/

/-- **The resolved path keeps the document root as a prefix** — structural
form. No request target, however many encoded or literal `..` it carries,
resolves outside the root. -/
theorem static_root_prefix (cfg : Config) (req : Req) :
    cfg.docRoot <+: resolvePath cfg req :=
  Safety.Traversal.serveStatic_root_prefix cfg.docRoot req.target

/-- **`static_no_escape`.** Even under a filesystem walker that actually pops
a component on `..` (`Route.Path.descend`), a clean document root stays a
prefix of the resolved path: the attacker's encoded `..` was removed before
resolution, so no pop ever fires above the root. -/
theorem static_no_escape (cfg : Config) (req : Req)
    (hclean : ∀ s ∈ cfg.docRoot, ¬ Route.Path.IsDot s) :
    cfg.docRoot <+: Route.Path.descend [] (resolvePath cfg req) :=
  Safety.Traversal.serveStatic_no_escape cfg.docRoot req.target hclean

/-! ## Conditional requests (RFC 7232 §3.2) -/

/-- **`conditional_304`.** When an `If-None-Match` tag weak-matches the
current entity-tag, the handler responds `304 (Not Modified)` — status
`304`, and an EMPTY body (RFC 7232 §3.2: respond with 304 for GET/HEAD, and
§4.1: a 304 does not carry content). -/
theorem conditional_304 (cfg : Config) (req : Req) (path : List String)
    (body : Bytes) (hfile : cfg.fs path = some body)
    (hmatch : ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = true) :
    serveResolved cfg req path = .notModified (cfg.etag path) ∧
    (serveResolved cfg req path).status = 304 ∧
    (serveResolved cfg req path).body = [] := by
  have hserve : serveResolved cfg req path = .notModified (cfg.etag path) := by
    unfold serveResolved
    rw [hfile]
    simp only [hmatch, if_true]
  refine ⟨hserve, ?_, ?_⟩ <;> rw [hserve] <;> rfl

/-! ## Range requests (RFC 7233 §4.1, §4.4) -/

/-- **`range_exact`.** A satisfiable range on a file (with the precondition
NOT firing) yields `206 (Partial Content)` whose body is exactly the byte
sub-slice `bytes[start .. end]` — and that body has length `end-start+1`,
the RFC 7233 §4.1 partial length. -/
theorem range_exact (cfg : Config) (req : Req) (path : List String)
    (body : Bytes) (spec : RangeSpec) (s e : Nat)
    (hfile : cfg.fs path = some body)
    (hnm : ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = false)
    (hrange : req.range = some spec)
    (hres : resolveRange body.length spec = some (s, e)) :
    serveResolved cfg req path
        = .partialContent (slice body s e) s e body.length (cfg.etag path) ∧
    (serveResolved cfg req path).body = slice body s e ∧
    (serveResolved cfg req path).body = (body.drop s).take (e - s + 1) ∧
    (serveResolved cfg req path).body.length = e - s + 1 := by
  have hle := resolveRange_valid body.length spec s e hres
  have hserve : serveResolved cfg req path
      = .partialContent (slice body s e) s e body.length (cfg.etag path) := by
    simp only [serveResolved, hfile, hnm, hrange, hres, Bool.false_eq_true, if_false]
  refine ⟨hserve, ?_, ?_, ?_⟩
  · rw [hserve]; rfl
  · rw [hserve]; rfl
  · rw [hserve]
    show (slice body s e).length = e - s + 1
    exact slice_length body s e hle.1 hle.2

/-- **`range_unsatisfiable`.** An invalid or unsatisfiable range (with the
precondition not firing) yields `416 (Range Not Satisfiable)` carrying the
complete length (RFC 7233 §4.4). -/
theorem range_unsatisfiable (cfg : Config) (req : Req) (path : List String)
    (body : Bytes) (spec : RangeSpec)
    (hfile : cfg.fs path = some body)
    (hnm : ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = false)
    (hrange : req.range = some spec)
    (hres : resolveRange body.length spec = none) :
    serveResolved cfg req path = .rangeNotSatisfiable body.length ∧
    (serveResolved cfg req path).status = 416 := by
  have hserve : serveResolved cfg req path = .rangeNotSatisfiable body.length := by
    simp only [serveResolved, hfile, hnm, hrange, hres, Bool.false_eq_true, if_false]
  exact ⟨hserve, by rw [hserve]; rfl⟩

/-! ## try_files and SPA fallback -/

/-- **try_files**: try an ordered list of candidate paths, serve the first
one that exists on the filesystem; if none exists, fall back to `fallback`. -/
def tryFiles (cfg : Config) (candidates : List (List String))
    (fallback : List String) : List String :=
  match candidates.find? (fun c => (cfg.fs c).isSome) with
  | some c => c
  | none => fallback

/-- `find?` returns the first list element satisfying the predicate: given a
split `pre ++ c :: post` where nothing in `pre` satisfies `p` and `c` does,
the result is `c`. -/
theorem find?_first {α} (p : α → Bool) (pre : List α) (c : α) (post : List α)
    (hpre : ∀ x ∈ pre, p x = false) (hc : p c = true) :
    (pre ++ c :: post).find? p = some c := by
  induction pre with
  | nil => simp [List.find?_cons, hc]
  | cons a pre' ih =>
    have ha : p a = false := hpre a (List.mem_cons_self a pre')
    have hpre' : ∀ x ∈ pre', p x = false :=
      fun x hx => hpre x (List.mem_cons_of_mem a hx)
    simp [List.find?_cons, ha, ih hpre']

/-- **`try_files_first`.** `tryFiles` serves the FIRST existing candidate:
given candidates `pre ++ c :: post` where no earlier candidate `pre` exists
and `c` does exist, the served path is exactly `c`. -/
theorem try_files_first (cfg : Config) (pre : List (List String))
    (c : List String) (post : List (List String)) (fallback : List String)
    (hpre : ∀ x ∈ pre, (cfg.fs x).isSome = false)
    (hc : (cfg.fs c).isSome = true) :
    tryFiles cfg (pre ++ c :: post) fallback = c := by
  unfold tryFiles
  rw [find?_first (fun c => (cfg.fs c).isSome) pre c post hpre hc]

/-- **SPA resolution**: an existing target serves itself; anything else
falls back to the single-page-application index. -/
def spaResolve (cfg : Config) (target index : List String) : List String :=
  if (cfg.fs target).isSome then target else index

/-- **`spa_fallback_unmatched`.** An unmatched (non-existent) target resolves
to the SPA index, never `404`. -/
theorem spa_fallback_unmatched (cfg : Config) (target index : List String)
    (h : (cfg.fs target).isSome = false) :
    spaResolve cfg target index = index := by
  unfold spaResolve; rw [h]; rfl

/-- An existing target serves itself (SPA fallback never masks a real file). -/
theorem spa_serves_existing (cfg : Config) (target index : List String)
    (h : (cfg.fs target).isSome = true) :
    spaResolve cfg target index = target := by
  unfold spaResolve; rw [h]; rfl

/-! ## Autoindex -/

/-- **`autoindex_only_dir`.** A directory listing response is produced only
when there is no regular file at the path AND the path is a directory. -/
theorem autoindex_only_dir (cfg : Config) (req : Req) (path : List String)
    (entries : List String)
    (h : serveResolved cfg req path = .autoindex entries) :
    cfg.fs path = none ∧ cfg.isDir path = true ∧ cfg.readDir path = entries := by
  unfold serveResolved at h
  cases hfs : cfg.fs path with
  | none =>
    rw [hfs] at h
    by_cases hdir : cfg.isDir path
    · simp only [hdir, if_true] at h
      cases h; exact ⟨rfl, hdir, rfl⟩
    · simp only [hdir, if_false] at h
      exact absurd h (by simp)
  | some body =>
    rw [hfs] at h
    -- the `some` branch can only produce notModified / ok / partial / 416
    simp only at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h <;> exact absurd h (by simp)

/-! ## Conditional gates: If-Modified-Since and If-Range (RFC 7232 §3.3, 7233 §3.2)

The richer selection layer `serveConditional` adds the two validators the single-
range core (`serveResolved`) left as boundary, plus a `multipart/byteranges`
body for a multi-range request. Its precedence is the RFC's: `If-None-Match`
first (RFC 7232 §6 — an entity-tag precondition overrides a date one), then
`If-Modified-Since`, then the `If-Range` eligibility gate on the range, then the
range-set itself. -/

/-- `If-Modified-Since` (RFC 7232 §3.3): a `304` is owed iff the representation's
`Last-Modified` is at or before the client's date — i.e. it has NOT been modified
since. An absent header never yields `304`. -/
def ifModifiedSince304 (lastMod : Nat) : Option Nat → Bool
  | none => false
  | some ims => decide (lastMod ≤ ims)

/-- `If-Range` eligibility (RFC 7233 §3.2): the range is honored only if the
`If-Range` validator still matches the current representation.
  * an entity-tag validator must match under the STRONG comparison (a weak tag is
    never eligible — RFC 7233 §3.2);
  * a date validator is eligible iff it equals the current `Last-Modified`;
  * an absent `If-Range` leaves the range eligible.
When ineligible, the whole representation (`200`) is served instead. -/
def ifRangeEligible (cur : ETag) (lastMod : Nat) : Option IfRange → Bool
  | none => true
  | some (.etag t) => t.strongMatch cur
  | some (.date d) => decide (lastMod = d)

/-! ## Multi-range resolution (RFC 7233 §4.1 `multipart/byteranges`) -/

/-- Resolve every spec in a range-set against a representation of length `L`,
keeping only the satisfiable ones (RFC 7233 §4.1: unsatisfiable members of a set
are dropped; an all-unsatisfiable set is a `416`). -/
def resolveAll (L : Nat) : List RangeSpec → List (Nat × Nat)
  | [] => []
  | spec :: rest =>
    match resolveRange L spec with
    | some p => p :: resolveAll L rest
    | none => resolveAll L rest

/-- Build the `multipart/byteranges` parts: each satisfiable `(start,end)` pair
becomes a part carrying its exact sub-slice and its inclusive offsets. -/
def mkParts (b : Bytes) : List (Nat × Nat) → List (Bytes × Nat × Nat)
  | [] => []
  | (s, e) :: rest => (slice b s e, s, e) :: mkParts b rest

/-- Every resolved pair in a range-set is well-formed: `start ≤ end < L`
(pointwise `resolveRange_valid`). -/
theorem resolveAll_valid (L : Nat) (specs : List RangeSpec) :
    ∀ pr ∈ resolveAll L specs, pr.1 ≤ pr.2 ∧ pr.2 < L := by
  induction specs with
  | nil => intro pr hpr; simp [resolveAll] at hpr
  | cons spec rest ih =>
    intro pr hpr
    simp only [resolveAll] at hpr
    cases hr : resolveRange L spec with
    | none => rw [hr] at hpr; exact ih pr hpr
    | some q =>
      rw [hr, List.mem_cons] at hpr
      cases hpr with
      | inl h => subst h; exact resolveRange_valid L spec pr.1 pr.2 (by rw [hr])
      | inr h => exact ih pr h

/-- Each built part carries the exact slice of its offsets and remembers those
offsets came from the resolved set. -/
theorem mkParts_mem (b : Bytes) (pairs : List (Nat × Nat)) :
    ∀ p ∈ mkParts b pairs, p.1 = slice b p.2.1 p.2.2 ∧ (p.2.1, p.2.2) ∈ pairs := by
  induction pairs with
  | nil => intro p hp; simp [mkParts] at hp
  | cons pr rest ih =>
    intro p hp
    obtain ⟨s, e⟩ := pr
    simp only [mkParts, List.mem_cons] at hp
    cases hp with
    | inl h => subst h; exact ⟨rfl, by simp⟩
    | inr h => obtain ⟨h1, h2⟩ := ih p h; exact ⟨h1, List.mem_cons_of_mem _ h2⟩

/-- **`multipart_ranges_exact`.** Every part of a `multipart/byteranges` body is
exactly the byte sub-slice of its declared offsets, those offsets are in range
(`start ≤ end < length`), and the part has the RFC 7233 §4.1 partial length
`end − start + 1`. This is the multi-range analogue of `range_exact`. -/
theorem multipart_ranges_exact (body : Bytes) (specs : List RangeSpec) :
    ∀ p ∈ mkParts body (resolveAll body.length specs),
      p.1 = slice body p.2.1 p.2.2 ∧
      p.2.1 ≤ p.2.2 ∧ p.2.2 < body.length ∧
      p.1.length = p.2.2 - p.2.1 + 1 := by
  intro p hp
  obtain ⟨hslice, hmem⟩ := mkParts_mem body _ p hp
  have hval := resolveAll_valid body.length specs (p.2.1, p.2.2) hmem
  refine ⟨hslice, hval.1, hval.2, ?_⟩
  rw [hslice]; exact slice_length body p.2.1 p.2.2 hval.1 hval.2

/-! ## The conditional handler -/

/-- The richer response selection: `If-None-Match` (as in the core), then
`If-Modified-Since`, then the `If-Range` gate, then the range-set (`[]` = no
`Range`; one satisfiable spec = a single `206`; several = `multipart/byteranges`;
none satisfiable = `416`). A missing file still falls to a listing or `404`. -/
def serveConditional (cfg : Config) (req : Req) (path : List String) : Resp :=
  match cfg.fs path with
  | none => if cfg.isDir path then .autoindex (cfg.readDir path) else .notFound
  | some body =>
    let cur := cfg.etag path
    let lm := cfg.lastModified path
    if ifNoneMatchHit req.ifNoneMatch cur then .notModified cur
    else if ifModifiedSince304 lm req.ifModifiedSince then .notModified cur
    else if !ifRangeEligible cur lm req.ifRange then .ok body cur
    else match req.rangeSet with
      | [] => .ok body cur
      | r :: rs =>
        match resolveAll body.length (r :: rs) with
        | [] => .rangeNotSatisfiable body.length
        | [(s, e)] => .partialContent (slice body s e) s e body.length cur
        | parts => .multipartRanges (mkParts body parts) body.length cur

/-- **`if_modified_since_304`.** With no `If-None-Match` hit, a representation
whose `Last-Modified` is at or before the client's `If-Modified-Since` yields
`304 (Not Modified)` — status `304`, empty body (RFC 7232 §3.3, §4.1). -/
theorem if_modified_since_304 (cfg : Config) (req : Req) (path : List String) (body : Bytes)
    (hfile : cfg.fs path = some body)
    (hnm : ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = false)
    (hims : ifModifiedSince304 (cfg.lastModified path) req.ifModifiedSince = true) :
    serveConditional cfg req path = .notModified (cfg.etag path) ∧
    (serveConditional cfg req path).status = 304 ∧
    (serveConditional cfg req path).body = [] := by
  have hserve : serveConditional cfg req path = .notModified (cfg.etag path) := by
    simp only [serveConditional, hfile, hnm, hims, Bool.false_eq_true, if_false, if_true]
  refine ⟨hserve, ?_, ?_⟩ <;> rw [hserve] <;> rfl

/-- **`if_range_weak_full`.** A WEAK entity-tag in `If-Range` makes the range
ineligible: the full representation (`200`) is served, never a `206`
(RFC 7233 §3.2 — only a strong validator gates a range). -/
theorem if_range_weak_full (cfg : Config) (req : Req) (path : List String) (body : Bytes)
    (t : ETag)
    (hfile : cfg.fs path = some body)
    (hnm : ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = false)
    (hims : ifModifiedSince304 (cfg.lastModified path) req.ifModifiedSince = false)
    (hir : req.ifRange = some (.etag t)) (hweak : t.weak = true) :
    serveConditional cfg req path = .ok body (cfg.etag path) := by
  have helig : ifRangeEligible (cfg.etag path) (cfg.lastModified path) req.ifRange = false := by
    rw [hir]; simp [ifRangeEligible, ETag.strongMatch, hweak]
  simp only [serveConditional, hfile, hnm, hims, helig, Bool.false_eq_true, if_false,
    Bool.not_false, if_true]

/-- An `If-Range` date is eligible exactly when it equals the current
`Last-Modified` (RFC 7233 §3.2). -/
theorem ifRange_date_eligible (cur : ETag) (lm d : Nat) (h : lm = d) :
    ifRangeEligible cur lm (some (.date d)) = true := by
  simp [ifRangeEligible, h]

/-- A STRONG entity-tag that matches is eligible (RFC 7232 §2.3.2 strong
comparison): neither weak, opaque tags equal. -/
theorem ifRange_strong_eligible (cur t : ETag)
    (hw1 : t.weak = false) (hw2 : cur.weak = false) (ht : t.tag = cur.tag) (lm : Nat) :
    ifRangeEligible cur lm (some (.etag t)) = true := by
  simp [ifRangeEligible, ETag.strongMatch, hw1, hw2, ht]

/-- **`serveConditional_multipart`.** When the gates pass and a range-set has at
least two satisfiable specs, the response is a `multipart/byteranges` `206` whose
parts are `mkParts` of the resolved offsets — combine with `multipart_ranges_exact`
for the per-part exactness. -/
theorem serveConditional_multipart (cfg : Config) (req : Req) (path : List String) (body : Bytes)
    (r : RangeSpec) (rs : List RangeSpec) (p1 p2 : Nat × Nat) (rest : List (Nat × Nat))
    (hfile : cfg.fs path = some body)
    (hnm : ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = false)
    (hims : ifModifiedSince304 (cfg.lastModified path) req.ifModifiedSince = false)
    (helig : ifRangeEligible (cfg.etag path) (cfg.lastModified path) req.ifRange = true)
    (hset : req.rangeSet = r :: rs)
    (hres : resolveAll body.length (r :: rs) = p1 :: p2 :: rest) :
    serveConditional cfg req path
      = .multipartRanges (mkParts body (p1 :: p2 :: rest)) body.length (cfg.etag path) := by
  simp only [serveConditional, hfile, hnm, hims, helig, Bool.false_eq_true, if_false,
    Bool.not_true, hset, hres]

/-- **`serveConditional_single`.** A range-set with exactly one satisfiable spec
collapses to a single-range `206` (RFC 7233 §4.1: `multipart/byteranges` is only
for more than one range). -/
theorem serveConditional_single (cfg : Config) (req : Req) (path : List String) (body : Bytes)
    (r : RangeSpec) (rs : List RangeSpec) (s e : Nat)
    (hfile : cfg.fs path = some body)
    (hnm : ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = false)
    (hims : ifModifiedSince304 (cfg.lastModified path) req.ifModifiedSince = false)
    (helig : ifRangeEligible (cfg.etag path) (cfg.lastModified path) req.ifRange = true)
    (hset : req.rangeSet = r :: rs)
    (hres : resolveAll body.length (r :: rs) = [(s, e)]) :
    serveConditional cfg req path
      = .partialContent (slice body s e) s e body.length (cfg.etag path) := by
  simp only [serveConditional, hfile, hnm, hims, helig, Bool.false_eq_true, if_false,
    Bool.not_true, hset, hres]

/-! ## Concrete witnesses (RFC 7233 §2.1 worked examples) -/

/-- RFC 7233 §2.1: for a representation of length 10000, the final 500 bytes
are offsets `9500-9999`. -/
theorem range_suffix_example :
    resolveRange 10000 (.suffix 500) = some (9500, 9999) := by decide

/-- RFC 7233 §2.1: `bytes=9500-` on length 10000 is the same `9500-9999`. -/
theorem range_fromOnly_example :
    resolveRange 10000 (.fromOnly 9500) = some (9500, 9999) := by decide

/-- A `last-byte-pos` beyond the representation is clamped to the last byte
(RFC 7233 §2.1 "remainder" rule): `bytes=500-99999` on length 8000 → `500-7999`. -/
theorem range_clamp_example :
    resolveRange 8000 (.fromTo 500 99999) = some (500, 7999) := by decide

/-- An out-of-range start is unsatisfiable → `416` (RFC 7233 §2.1, §4.4). -/
theorem range_unsat_example :
    resolveRange 100 (.fromOnly 500) = none := by decide

/-- A concrete slice: bytes `[0,1,2,3,4]`, range `1-3`, yields `[1,2,3]`. -/
theorem slice_example :
    slice [0, 1, 2, 3, 4] 1 3 = [1, 2, 3] := by decide

/-- Weak comparison ignores the `W/` flag (RFC 7232 §2.3.2 table row
`W/"1"` vs `"1"` → match). -/
theorem weak_match_ignores_flag :
    ETag.weakMatch ⟨true, "1"⟩ ⟨false, "1"⟩ = true := by decide

/-- Differing opaque tags never match, weak or not. -/
theorem weak_match_distinguishes :
    ETag.weakMatch ⟨true, "1"⟩ ⟨true, "2"⟩ = false := by decide

end StaticFile

#print axioms StaticFile.multipart_ranges_exact
#print axioms StaticFile.if_modified_since_304
#print axioms StaticFile.if_range_weak_full
#print axioms StaticFile.serveConditional_multipart
#print axioms StaticFile.range_exact
#print axioms StaticFile.static_no_escape
