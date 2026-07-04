/-
Header — hop-by-hop stripping as a partition identity.

`strip hop` (defined in `Header/Basic.lean`) filters a header list on the
predicate "name is not in the hop set `hop`".  A filter partitions its input:
every field is either dropped (name in `hop`) or kept (name not in `hop`), and
nothing is invented or duplicated.  This file states that partition precisely.

  * `mem_strip`         — membership characterisation: a field survives iff it
                          was present and is not a hop header.
  * `strip_survives`    — every end-to-end (non-hop) field survives.
  * `strip_hop_removed` — no hop field survives.
  * `strip_subset`      — nothing is invented.
  * `strip_partition`   — the accounting identity: `#kept + #stripped = #total`.
  * `get_strip_hop`     — a lookup of any hop name after stripping is absent.
  * `strip_idem`        — stripping twice equals stripping once.

The set of hop names is a parameter, so the result holds for any policy's hop
list.  `hopStd` instantiates it with the RFC 7230 §6.1 connection-management
headers, and the worked vectors at the end are checked by the kernel (`decide`),
including a case-varied `Connection` header to exhibit the case-insensitive
match.
-/

import Header.Basic

namespace Header

/-! ### `strip` reduction and membership -/

theorem strip_cons (hop : List Name) (f : Field) (t : Headers) :
    strip hop (f :: t) = if isHop hop f.name then strip hop t else f :: strip hop t := by
  simp only [strip, List.filter_cons]
  by_cases hb : isHop hop f.name = true
  · rw [if_pos hb]; simp [hb]
  · rw [if_neg hb]; simp [eq_false_of_ne_true hb]

/-- **Membership characterisation.**  A field survives the strip exactly when it
was present and is not a hop header. -/
theorem mem_strip {hop : List Name} {h : Headers} {f : Field} :
    f ∈ strip hop h ↔ f ∈ h ∧ isHop hop f.name = false := by
  simp only [strip, List.mem_filter]
  by_cases hb : isHop hop f.name = true
  · simp [hb]
  · simp [eq_false_of_ne_true hb]

/-- **End-to-end fields survive.**  Any non-hop field of the input is retained. -/
theorem strip_survives {hop : List Name} {h : Headers} {f : Field}
    (hh : f ∈ h) (hn : isHop hop f.name = false) : f ∈ strip hop h :=
  mem_strip.mpr ⟨hh, hn⟩

/-- **No hop field survives.**  A surviving field is never a hop header. -/
theorem strip_no_hop {hop : List Name} {h : Headers} {f : Field}
    (hf : f ∈ strip hop h) : isHop hop f.name = false :=
  (mem_strip.mp hf).2

/-- **Nothing is invented.**  Every surviving field came from the input. -/
theorem strip_subset {hop : List Name} {h : Headers} {f : Field}
    (hf : f ∈ strip hop h) : f ∈ h :=
  (mem_strip.mp hf).1

/-- A hop header is removed: it is not among the survivors. -/
theorem strip_hop_removed {hop : List Name} {h : Headers} {f : Field}
    (hn : isHop hop f.name = true) : f ∉ strip hop h := by
  intro hf
  rw [strip_no_hop hf] at hn
  exact absurd hn (by decide)

/-- **The partition identity.**  The survivors and the stripped fields together
account for exactly the input: `#kept + #stripped = #total`. -/
theorem strip_partition (hop : List Name) (h : Headers) :
    (strip hop h).length + (h.filter (fun f => isHop hop f.name)).length = h.length := by
  induction h with
  | nil => rfl
  | cons f t ih =>
    rw [strip_cons, List.filter_cons]
    by_cases hb : isHop hop f.name = true
    · rw [if_pos hb, if_pos hb]; simp only [List.length_cons]; omega
    · rw [if_neg hb, if_neg hb]; simp only [List.length_cons]; omega

/-- **`strip` is idempotent.** -/
theorem strip_idem (hop : List Name) (h : Headers) :
    strip hop (strip hop h) = strip hop h := by
  simp only [strip, List.filter_filter, Bool.and_self]

/-! ### Lookups of hop names go absent -/

/-- `isHop` is invariant under case-insensitive name equality. -/
theorem isHop_congr {hop : List Name} {a b : Name} (h : nameEqb a b = true) :
    isHop hop a = isHop hop b := by
  unfold isHop
  have hfun : (fun hn => nameEqb hn a) = (fun hn => nameEqb hn b) := by
    funext hn; exact nameEqb_congr_right h hn
  rw [hfun]

/-- **A hop lookup is absent after stripping.**  For any hop name `n`, `get n`
returns `none` on a stripped list — the hop header is gone, and no other
(surviving) field can match a hop name. -/
theorem get_strip_hop {hop : List Name} {n : Name} (h : Headers)
    (hn : isHop hop n = true) : get n (strip hop h) = none := by
  have H : ∀ f ∈ strip hop h, nameEqb f.name n = false := by
    intro f hf
    cases hc : nameEqb f.name n with
    | false => rfl
    | true =>
      exfalso
      have h1 : isHop hop f.name = true := by rw [isHop_congr hc]; exact hn
      have h2 : isHop hop f.name = false := strip_no_hop hf
      rw [h1] at h2; exact absurd h2 (by decide)
  unfold get
  rw [find?_none_of_all (fun f => nameEqb f.name n) (strip hop h) H]
  rfl

/-! ### The RFC 7230 §6.1 hop set, and worked vectors

`hopStd` is the connection-management header set that must not be forwarded
end-to-end.  The names are stored lower-cased; the case-insensitive match makes
`Connection` (capital `C`) still count as a hop header. -/

/-- RFC 7230 §6.1 hop-by-hop header names (lower-cased byte-strings). -/
def hopStd : List Name :=
  [ [99,111,110,110,101,99,116,105,111,110],                          -- "connection"
    [107,101,101,112,45,97,108,105,118,101],                          -- "keep-alive"
    [112,114,111,120,121,45,97,117,116,104,101,110,116,105,99,97,116,101],        -- "proxy-authenticate"
    [112,114,111,120,121,45,97,117,116,104,111,114,105,122,97,116,105,111,110],   -- "proxy-authorization"
    [112,114,111,120,121,45,99,111,110,110,101,99,116,105,111,110],               -- "proxy-connection"
    [116,101],                                                         -- "te"
    [116,114,97,105,108,101,114],                                      -- "trailer"
    [116,114,97,110,115,102,101,114,45,101,110,99,111,100,105,110,103],           -- "transfer-encoding"
    [117,112,103,114,97,100,101] ]                                     -- "upgrade"

/-- `Connection: close` — note the capital `C`. -/
def exConn : Field := ⟨[67,111,110,110,101,99,116,105,111,110], [99,108,111,115,101]⟩

/-- `Content-Type: text`. -/
def exCT : Field := ⟨[67,111,110,116,101,110,116,45,84,121,112,101], [116,101,120,116]⟩

/-- `X-Trace: 1`. -/
def exXT : Field := ⟨[88,45,84,114,97,99,101], [49]⟩

/-- A three-field header list: one hop header, two end-to-end headers. -/
def exHeaders : Headers := [exConn, exCT, exXT]

/-- Case-insensitive match: the lower-cased `hopStd` recognises capital-`C`
`Connection` as a hop header. -/
example : isHop hopStd exConn.name = true := by decide

/-- `Content-Type` is not a hop header. -/
example : isHop hopStd exCT.name = false := by decide

/-- Stripping removes exactly `Connection`, preserving the rest in order. -/
example : strip hopStd exHeaders = [exCT, exXT] := by decide

/-- The partition identity, instantiated: `2 kept + 1 stripped = 3 total`. -/
example :
    (strip hopStd exHeaders).length
      + (exHeaders.filter (fun f => isHop hopStd f.name)).length
      = exHeaders.length :=
  strip_partition hopStd exHeaders

/-- A lookup of the (lower-case) hop name after stripping is absent — via the
general theorem, with the hop-membership side condition checked by the kernel. -/
example : get [99,111,110,110,101,99,116,105,111,110] (strip hopStd exHeaders) = none :=
  get_strip_hop exHeaders (by decide)

/-- An end-to-end header survives with its value intact. -/
example : get exCT.name (strip hopStd exHeaders) = some exCT.value := by decide

end Header
