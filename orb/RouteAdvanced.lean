/-
RouteAdvanced — a richer request router: virtual hosts (server-blocks) with
SNI-style host selection, host-glob matching, per-segment path matching with
exact / `*` (one segment) / abstract-regex kinds, a recursive `**` suffix glob,
and header-required / query-required guards, all as one total, deterministic,
first-match dispatch function.

This is a strict superset of the shape in `Route.Match` (which had only
exact/prefix/default over a flat table). Here the table is two-level: a list of
`ServerBlock`s keyed by a host pattern, each holding an ordered list of routes.
Dispatch picks the FIRST block whose host matches the request authority (the
SNI/Host selection), then the FIRST route in that block that matches — a plain
`List.find?` at each level, so first-match determinism holds by construction.

RFC sections captured
---------------------
* RFC 9110 §7.2 (Host and :authority) — the host/authority is "an application-
  level routing mechanism" that lets one server "distinguish among resources
  while servicing requests for multiple host names". That is exactly the
  server-block / virtual-host selection modeled by `selectBlock`.
* RFC 9110 §7.4 (Rejecting Misdirected Requests / 421) — a request whose host
  does not match the block it would be served by is misdirected and MUST NOT be
  served by that block. `route_host_isolation` is this property: a block bound
  to an exact host B is never selected for a request whose host is not B.
* RFC 9110 §9 / §9.3 (Methods) — the request method is matched (`anyMethod` or a
  specific token); method values are case-sensitive tokens, compared literally.
* RFC 9112 §3.2 and RFC 3986 §3.3 (path / segments) — the path is matched as an
  already-split segment list (the split/normalize is `Route.Path`'s job).
* RFC 3986 §3.4 (Query) — query is a list of key/value pairs; `queryPresent`
  and `queryEquals` are "query-required" guards.
* RFC 6066 §3 (Server Name Indication) — host-based block selection mirrors SNI:
  the authoritative host chosen at the TLS layer selects the virtual server.

Boundaries / UNCLOSED
---------------------
* REGEX is an abstract total predicate `String → Bool` (`SegPat.rx`). We do NOT
  implement a regex engine — any total single-segment matcher plugs in, and
  every theorem holds uniformly over all of them (the same named-boundary
  discipline `Tls` uses for crypto). A regex that does not terminate is out of
  model; the boundary is "total decision procedure for one segment".
* HOST/SNI EXTRACTION is a boundary: the request's authoritative host arrives as
  an already-split, already-normalized label list (`Req.host`). The TLS SNI
  extension parse, the RFC 9110 §7.2 Host-header ABNF parse, port stripping, and
  the case-folding of scheme/host (RFC 9110 §1179) happen upstream.
* FIELD-NAME CASE-INSENSITIVITY (RFC 9110 §5.1: "Field names are case-
  insensitive") is UNCLOSED here: `headerPresent`/`headerEquals` compare names
  literally. A case-normalizing boundary (lower-casing names before they reach
  the guard) restores the RFC semantics; that normalization is not modeled.
* PATH NORMALIZATION (percent-decode once, RFC 3986 §5.2.4 dot-segment removal)
  is handled by the sibling `Route.Path` library and assumed already applied to
  `Req.segs`; it is not re-derived here.

Theorems
--------
* `route_first_match` / `dispatch_first_match` — the first matching route in the
  selected block wins: the result splits the route list as `pre ++ r :: suf`
  with every route in `pre` failing to match and `r` matching. `dispatch_deterministic`
  states the obvious consequence: the result is unique.
* `route_host_isolation` — a request for host A is never served by a block bound
  only to (exact) host B; `selectBlock` cannot return that block.
* `glob_matches_correct` bundle — `star_matches_single` / `star_consumes_one`
  (`*` matches exactly one segment), and `matchPrefixSegs_append` /
  `matchPrefixSegs_split` (`**` matches ANY suffix: a globstar pattern matches
  `req` iff its segments match some prefix of `req`).
* `route_catchall` — an all-permissive block+route (`anyHost`, `anyMethod`,
  empty `**` path, no guards) matches every request.

All crypto/regex/host-parse content is a total uninterpreted boundary; no cipher
or regex engine is implemented. Core-only Lean (no Mathlib).
-/

namespace RouteAdvanced

/-! ## Per-segment match kinds -/

/-- A single path-segment matcher. `lit` is exact string equality; `star` is the
`*` wildcard that matches exactly one arbitrary segment; `rx` is an ABSTRACT
total regex predicate over one segment (the named boundary — no engine here). -/
inductive SegPat where
  | lit (s : String)
  | star
  | rx (m : String → Bool)

/-- Match one segment pattern against one segment. -/
def segMatch : SegPat → String → Bool
  | .lit s, x => decide (x = s)
  | .star, _ => true
  | .rx f, x => f x

/-- `*` matches ANY single segment. -/
theorem star_matches_any (s : String) : segMatch SegPat.star s = true := rfl

/-! ## Full-length pointwise match and prefix (globstar) match -/

/-- `matchAll ps req`: the pattern list matches the request segment list
one-for-one, same length. This is the `**`-free "exact structure" match. -/
def matchAll : List SegPat → List String → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | p :: ps, x :: xs => segMatch p x && matchAll ps xs

/-- `matchPrefixSegs ps req`: `ps` matches a PREFIX of `req`; the remaining
segments are unconstrained. This is the meaning of a trailing `**`: the explicit
segments pin down the start, and `**` absorbs any suffix. -/
def matchPrefixSegs : List SegPat → List String → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, x :: xs => segMatch p x && matchPrefixSegs ps xs

/-! ### `glob_matches_correct` — `*` is one segment, `**` is any suffix -/

/-- `*` alone matches a one-segment request. -/
theorem star_matches_single (s : String) :
    matchAll [SegPat.star] [s] = true := by
  simp [matchAll, segMatch]

/-- `*` alone matches ONLY one-segment requests: a `star` pattern consumes
exactly one segment, never zero and never two. -/
theorem star_consumes_one {req : List String}
    (h : matchAll [SegPat.star] req = true) : ∃ s, req = [s] := by
  cases req with
  | nil => simp [matchAll] at h
  | cons x xs =>
    cases xs with
    | nil => exact ⟨x, rfl⟩
    | cons y ys => simp [matchAll, segMatch] at h

/-- **`**` matches any suffix (soundness).** If the explicit segments `ps` match
a segment list `front` exactly, then the globstar pattern matches `front`
followed by ANY suffix. -/
theorem matchPrefixSegs_append : ∀ {ps : List SegPat} {front : List String},
    matchAll ps front = true → ∀ suf, matchPrefixSegs ps (front ++ suf) = true := by
  intro ps
  induction ps with
  | nil => intro front _ suf; rfl
  | cons p ps' ih =>
    intro front h suf
    cases front with
    | nil => simp [matchAll] at h
    | cons x xs =>
      simp only [matchAll] at h
      rw [Bool.and_eq_true] at h
      show matchPrefixSegs (p :: ps') (x :: (xs ++ suf)) = true
      simp only [matchPrefixSegs]
      rw [Bool.and_eq_true]
      exact ⟨h.1, ih h.2 suf⟩

/-- **`**` matches any suffix (completeness).** Every request the globstar
pattern matches decomposes as `front ++ suf` where `front` (of length exactly
`ps.length`) is matched pointwise by the explicit segments and `suf` is the
absorbed suffix. Together with `matchPrefixSegs_append` this pins the semantics:
a globstar pattern matches `req` iff its segments match some prefix of `req`. -/
theorem matchPrefixSegs_split : ∀ {ps : List SegPat} {req : List String},
    matchPrefixSegs ps req = true →
    ∃ front suf, req = front ++ suf ∧ matchAll ps front = true
      ∧ front.length = ps.length := by
  intro ps
  induction ps with
  | nil => intro req _; exact ⟨[], req, rfl, rfl, rfl⟩
  | cons p ps' ih =>
    intro req h
    cases req with
    | nil => simp [matchPrefixSegs] at h
    | cons x xs =>
      simp only [matchPrefixSegs] at h
      rw [Bool.and_eq_true] at h
      obtain ⟨front, suf, heq, hall, hlen⟩ := ih h.2
      refine ⟨x :: front, suf, ?_, ?_, ?_⟩
      · simp [heq]
      · simp only [matchAll]; rw [Bool.and_eq_true]; exact ⟨h.1, hall⟩
      · simp [hlen]

/-! ## Compiled path pattern (segments + optional trailing `**`) -/

/-- A path pattern: an explicit sequence of segment matchers plus a `globstar`
flag. When `globstar` is set the sequence matches a prefix and a trailing `**`
absorbs the rest; otherwise the sequence must match the whole request length. -/
structure PathPat where
  segs : List SegPat
  globstar : Bool

/-- Match a compiled path pattern against a request's segment list. -/
def pathMatch (pp : PathPat) (req : List String) : Bool :=
  if pp.globstar then matchPrefixSegs pp.segs req else matchAll pp.segs req

/-- The empty globstar pattern (`**` alone) is the path catch-all: it matches
every request path. -/
theorem catchAllPath_matches (req : List String) :
    pathMatch { segs := [], globstar := true } req = true := rfl

/-! ## Method and host patterns -/

/-- Method matcher: any method, or a specific method token (RFC 9110 §9). -/
inductive MethodPat where
  | anyMethod
  | exact (m : String)

def methodMatch : MethodPat → String → Bool
  | .anyMethod, _ => true
  | .exact m, x => decide (x = m)

/-- Host pattern over already-split host labels (e.g. `["www","example","com"]`).
`anyHost` is the default/fallback server; `exact` pins the full label list;
`wild` is the leading-label wildcard `*.rest` — one arbitrary leading label
followed by `rest` (RFC 6066 §3 host selection, nginx-style `server_name`). -/
inductive HostPat where
  | anyHost
  | exact (labels : List String)
  | wild (rest : List String)

/-- Match a host pattern against a request's host label list. -/
def hostMatch : HostPat → List String → Bool
  | .anyHost, _ => true
  | .exact ls, req => decide (req = ls)
  | .wild rest, req =>
    match req with
    | _ :: tl => decide (tl = rest)
    | [] => false

/-- `anyHost` matches every authority. -/
theorem anyHost_matches (h : List String) : hostMatch HostPat.anyHost h = true := rfl

/-- An exact-host pattern does NOT match a different host. This is the pure
kernel of host isolation. -/
theorem hostMatch_exact_ne {hB reqHost : List String} (h : reqHost ≠ hB) :
    hostMatch (HostPat.exact hB) reqHost = false := by
  simp only [hostMatch]; exact decide_eq_false h

/-- The `*.rest` wildcard matches exactly the hosts with one extra leading label
over `rest` (and never the bare `rest` with no leading label). -/
theorem wild_matches_iff {rest req : List String} :
    hostMatch (HostPat.wild rest) req = true ↔ ∃ h, req = h :: rest := by
  cases req with
  | nil => simp [hostMatch]
  | cons h tl =>
    simp only [hostMatch]
    constructor
    · intro hh; exact ⟨h, by rw [of_decide_eq_true hh]⟩
    · intro ⟨h', hy⟩; cases hy; exact decide_eq_true rfl

/-! ## Request, route, server block -/

/-- A routed request. `host` is the pre-split authoritative host labels;
`segs` is the pre-normalized path segment list; `headers` and `query` are
key/value lists. -/
structure Req where
  host : List String
  method : String
  segs : List String
  headers : List (String × String)
  query : List (String × String)

/-- A guard is any total predicate over the request — the abstract boundary that
header-required / query-required (and any future condition) plug into. -/
abbrev Guard := Req → Bool

/-- A route: method + path pattern + ordered guards + a handler of type `H`. -/
structure Route (H : Type) where
  method : MethodPat
  path : PathPat
  guards : List Guard
  handler : H

/-- A virtual host / server block: a host pattern and its ordered routes. -/
structure ServerBlock (H : Type) where
  host : HostPat
  routes : List (Route H)

variable {H : Type}

/-- A route matches a request iff method, path, and every guard all pass. -/
def routeMatches (req : Req) (r : Route H) : Bool :=
  methodMatch r.method req.method && pathMatch r.path req.segs
    && r.guards.all (fun g => g req)

/-! ### Header-required / query-required guard constructors -/

/-- Guard: a header with the given name must be present. -/
def headerPresent (name : String) : Guard :=
  fun req => req.headers.any (fun kv => decide (kv.1 = name))

/-- Guard: a header with the given name and value must be present. -/
def headerEquals (name value : String) : Guard :=
  fun req => req.headers.any (fun kv => decide (kv.1 = name ∧ kv.2 = value))

/-- Guard: a query key must be present. -/
def queryPresent (key : String) : Guard :=
  fun req => req.query.any (fun kv => decide (kv.1 = key))

/-- Guard: a query key with the given value must be present. -/
def queryEquals (key value : String) : Guard :=
  fun req => req.query.any (fun kv => decide (kv.1 = key ∧ kv.2 = value))

/-! ## Dispatch: SNI-style block selection, then first-match routing -/

/-- Select the first server block whose host pattern matches the request
authority (the SNI/Host selection, RFC 9110 §7.2 / RFC 6066 §3). -/
def selectBlock (blocks : List (ServerBlock H)) (req : Req) : Option (ServerBlock H) :=
  blocks.find? (fun b => hostMatch b.host req.host)

/-- Full dispatch: pick the block by host, then the first matching route. -/
def dispatch (blocks : List (ServerBlock H)) (req : Req) : Option (Route H) :=
  match selectBlock blocks req with
  | none => none
  | some b => b.routes.find? (routeMatches req)

/-! ## List.find? — first-match characterization (self-contained, core only) -/

/-- `find?` returning `some a` splits the list as `pre ++ a :: suf` where every
element of `pre` fails the predicate and `a` satisfies it: the FIRST match. -/
theorem find?_split {α} {p : α → Bool} :
    ∀ {l : List α} {a : α}, l.find? p = some a →
      ∃ pre suf, l = pre ++ a :: suf ∧ (∀ x ∈ pre, p x = false) ∧ p a = true := by
  intro l
  induction l with
  | nil => intro a h; simp [List.find?] at h
  | cons b t ih =>
    intro a h
    cases hb : p b with
    | true =>
      rw [List.find?, hb] at h
      cases h
      refine ⟨[], t, rfl, ?_, hb⟩
      intro x hx; exact absurd hx (List.not_mem_nil x)
    | false =>
      rw [List.find?, hb] at h
      obtain ⟨pre, suf, heq, hpre, hpa⟩ := ih h
      refine ⟨b :: pre, suf, ?_, ?_, hpa⟩
      · simp [heq]
      · intro x hx
        rcases List.mem_cons.mp hx with h' | h'
        · subst h'; exact hb
        · exact hpre x h'

/-- `find?`-returned element satisfies the predicate. -/
theorem find?_true {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true := by
  obtain ⟨_, _, _, _, hpa⟩ := find?_split h; exact hpa

/-- `find?`-returned element is a member of the list. -/
theorem find?_mem {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l := by
  obtain ⟨pre, suf, heq, _, _⟩ := find?_split h
  rw [heq]; exact List.mem_append_right pre (List.mem_cons_self a suf)

/-! ## Host isolation -/

/-- The selected block's host actually matches the request authority. -/
theorem selectBlock_host_matches {blocks : List (ServerBlock H)} {req : Req}
    {b : ServerBlock H} (h : selectBlock blocks req = some b) :
    hostMatch b.host req.host = true := by
  unfold selectBlock at h
  have hb := find?_true h
  simpa using hb

/-- **Host isolation.** A request whose host is not `hB` is never served by a
block bound only to the exact host `hB`: `selectBlock` cannot return that block.
This is the RFC 9110 §7.4 no-misdirection property at the routing layer. -/
theorem route_host_isolation {blocks : List (ServerBlock H)} {req : Req}
    {b : ServerBlock H} {hB : List String}
    (hexact : b.host = HostPat.exact hB) (hne : req.host ≠ hB) :
    selectBlock blocks req ≠ some b := by
  intro hsel
  have hm := selectBlock_host_matches hsel
  rw [hexact, hostMatch_exact_ne hne] at hm
  exact Bool.noConfusion hm

/-! ## First-match determinism -/

/-- **First-match (block level).** Within the selected block, the chosen route
splits the route list as `pre ++ r :: suf` with every earlier route failing to
match and `r` matching: the earliest matching route wins. -/
theorem route_first_match {blocks : List (ServerBlock H)} {req : Req}
    {b : ServerBlock H} {r : Route H}
    (_hb : selectBlock blocks req = some b)
    (hr : b.routes.find? (routeMatches req) = some r) :
    ∃ pre suf, b.routes = pre ++ r :: suf
      ∧ (∀ r' ∈ pre, routeMatches req r' = false)
      ∧ routeMatches req r = true := find?_split hr

/-- **First-match (dispatch level).** The dispatched route is the first matching
route of the selected block. -/
theorem dispatch_first_match {blocks : List (ServerBlock H)} {req : Req}
    {r : Route H} (h : dispatch blocks req = some r) :
    ∃ b, selectBlock blocks req = some b ∧ ∃ pre suf,
      b.routes = pre ++ r :: suf
      ∧ (∀ r' ∈ pre, routeMatches req r' = false)
      ∧ routeMatches req r = true := by
  unfold dispatch at h
  cases hb : selectBlock blocks req with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; exact ⟨b, rfl, find?_split h⟩

/-- **Soundness.** A dispatched route actually matches the request. -/
theorem dispatch_sound {blocks : List (ServerBlock H)} {req : Req} {r : Route H}
    (h : dispatch blocks req = some r) : routeMatches req r = true := by
  unfold dispatch at h
  cases hb : selectBlock blocks req with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; exact find?_true h

/-- **Membership.** A dispatched route belongs to the selected block, whose host
matches the request. -/
theorem dispatch_block {blocks : List (ServerBlock H)} {req : Req} {r : Route H}
    (h : dispatch blocks req = some r) :
    ∃ b, selectBlock blocks req = some b ∧ r ∈ b.routes
      ∧ hostMatch b.host req.host = true := by
  unfold dispatch at h
  cases hb : selectBlock blocks req with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; exact ⟨b, rfl, find?_mem h, selectBlock_host_matches hb⟩

/-- **Determinism.** Dispatch is a function, so its result is unique. -/
theorem dispatch_deterministic {blocks : List (ServerBlock H)} {req : Req}
    {r r' : Route H} (h1 : dispatch blocks req = some r)
    (h2 : dispatch blocks req = some r') : r = r' := by
  rw [h1] at h2; exact Option.some.injEq r r' ▸ h2

/-! ## Guards are enforced (header-required / query-required are non-vacuous) -/

/-- Every element of an `all`-satisfied list satisfies the predicate. -/
theorem all_mem {α} {p : α → Bool} {l : List α}
    (h : l.all p = true) : ∀ x ∈ l, p x = true := by
  intro x hx
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with h' | h'
    · subst h'; exact h.1
    · exact ih h.2 h'

/-- A matching route has passed every one of its guards. -/
theorem routeMatches_guards {req : Req} {r : Route H}
    (h : routeMatches req r = true) : ∀ g ∈ r.guards, g req = true := by
  unfold routeMatches at h
  rw [Bool.and_eq_true] at h
  exact all_mem h.2

/-- **Header-required is enforced.** A route carrying a `headerPresent name`
guard cannot match a request that lacks that header. -/
theorem headerRequired_blocks {req : Req} {r : Route H} {name : String}
    (hguard : headerPresent name ∈ r.guards)
    (habsent : headerPresent name req = false) :
    routeMatches req r ≠ true := by
  intro h
  have hp := routeMatches_guards h (headerPresent name) hguard
  rw [habsent] at hp
  exact Bool.noConfusion hp

/-- **Query-required is enforced.** A route carrying a `queryPresent key` guard
cannot match a request that lacks that query key. -/
theorem queryRequired_blocks {req : Req} {r : Route H} {key : String}
    (hguard : queryPresent key ∈ r.guards)
    (habsent : queryPresent key req = false) :
    routeMatches req r ≠ true := by
  intro h
  have hp := routeMatches_guards h (queryPresent key) hguard
  rw [habsent] at hp
  exact Bool.noConfusion hp

/-! ## Catch-all -/

/-- The catch-all route: any method, `**` path, no guards. Matches everything. -/
def catchAllRoute (h : H) : Route H :=
  { method := MethodPat.anyMethod
    path := { segs := [], globstar := true }
    guards := []
    handler := h }

/-- The catch-all route matches every request. -/
theorem catchAllRoute_matches (h : H) (req : Req) :
    routeMatches req (catchAllRoute h) = true := by
  simp [routeMatches, catchAllRoute, methodMatch, pathMatch, matchPrefixSegs]

/-- The catch-all block: `anyHost`, holding the catch-all route. -/
def catchAllBlock (h : H) : ServerBlock H :=
  { host := HostPat.anyHost, routes := [catchAllRoute h] }

/-- **Catch-all.** A router consisting of a single catch-all block dispatches
every request to the catch-all route — the empty match matches everything. -/
theorem route_catchall (h : H) (req : Req) :
    dispatch [catchAllBlock h] req = some (catchAllRoute h) := by
  have hr := catchAllRoute_matches h req
  have hsel : selectBlock [catchAllBlock h] req = some (catchAllBlock h) :=
    List.find?_cons_of_pos [] rfl
  unfold dispatch
  rw [hsel]
  show (catchAllBlock h).routes.find? (routeMatches req) = some (catchAllRoute h)
  exact List.find?_cons_of_pos [] hr

end RouteAdvanced
