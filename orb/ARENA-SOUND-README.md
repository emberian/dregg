# Arena request-line soundness (`ArenaSound.lean`)

This file upgrades the arena parser's headline claim from a **safety** property
to a **correctness** property for the request line.

## The gap this closes

`parse_wf` (in `Arena/ParseTheorems.lean`) proves that every `complete` parse
outcome carries a **well-formed** store: each registered view range is in-bounds
of the arena it addresses. Its corollaries (`Store.resolve_total`,
`Store.resolve_length`) then give totality of `resolve` and that each field
resolves to exactly `len` bytes.

All of that is about **bounds and totality**. None of it constrains *which*
bytes a field denotes. A degenerate parser that returned empty-but-in-bounds
spans — every field `⟨off := 0, len := 0⟩` — would still satisfy `parse_wf`:
every range `[0,0)` is trivially in-bounds, `resolve` is total, and every field
resolves to the empty byte string. That parser is total nonsense, yet it passes
every theorem in `ParseTheorems.lean`. Safety cannot see the difference.

## What is now proven (correctness / meaning)

`ArenaSound.lean` states and proves the **meaning** successor. The headline
result is:

```
theorem Arena.Parse.parse_reqline_sound
    (h : parse input maxHeaders = .complete req) :
    ∃ (i₁ i₂ L : Nat),
      i₁ < L ∧ i₁ + 1 + i₂ < L ∧ L ≤ input.length ∧
      -- the two SP separators sit exactly at the reported offsets …
      input[i₁]? = some SP ∧
      input[i₁ + 1 + i₂]? = some SP ∧
      -- … and there is no earlier SP in the method or the target
      (∀ j, j < i₁ → input[j]? ≠ some SP) ∧
      (∀ j, i₁ < j → j < i₁ + 1 + i₂ → input[j]? ≠ some SP) ∧
      -- each resolved field EQUALS its exact input substring
      (∃ mb, req.store.resolve req.method  = some mb ∧ mb.toList = input.take i₁) ∧
      (∃ tb, req.store.resolve req.target  = some tb ∧
          tb.toList = (input.drop (i₁ + 1)).take i₂) ∧
      (∃ vb, req.store.resolve req.version = some vb ∧
          vb.toList = (input.drop (i₁ + 1 + i₂ + 1)).take (L - (i₁ + 1 + i₂ + 1))) ∧
      -- serialize-of-parse = input prefix
      (∀ mb tb vb, req.store.resolve req.method = some mb →
          req.store.resolve req.target = some tb →
          req.store.resolve req.version = some vb →
          mb.toList ++ SP :: (tb.toList ++ SP :: vb.toList) = input.take L)
```

Concretely, for any `complete` parse there are separator offsets `i₁`, `i₂` and
a request-line length `L` such that:

1. **Grammar agreement on the separators.** `input[i₁] = SP` and
   `input[i₁+1+i₂] = SP`, and no SP occurs earlier inside the method
   (`∀ j < i₁`) or inside the target (`∀ j, i₁ < j < i₁+1+i₂`). So `i₁` is
   genuinely the *first* SP and `i₁+1+i₂` the *second*, exactly as the RFC 9112
   request-line grammar `method SP request-target SP HTTP-version` requires.

2. **Field-extraction correctness.** Each resolved field equals its exact input
   substring — not merely a same-length byte range:
   * `method  = input[0, i₁)`
   * `target  = input[i₁+1, i₁+1+i₂)`
   * `version = input[i₁+1+i₂+1, L)`

3. **Serialize-of-parse = input prefix.** Re-concatenating the *resolved* field
   bytes with their SP separators reproduces the consumed request line exactly:
   `method ++ " " ++ target ++ " " ++ version = input.take L`. This is the
   round-trip statement in its strongest form — it is phrased over the bytes
   `resolve` actually returns, not over the spans.

The degenerate empty-span parser **fails** `parse_reqline_sound`: clause (1)
would force `input[0] = SP` (method boundary at offset 0), which is false for
any real request line such as `GET / HTTP/1.1`. Bounds could not rule it out;
meaning does.

### Supporting lemmas (all in `ArenaSound.lean`)

* `parseRequestLine_sound` — the field-extraction soundness of the line parser
  in isolation: the three spans denote the exact grammar fields of the line, the
  two SP separators sit at `i₁` / `i₁+1+i₂`, and no earlier SP occurs in method
  or target.
* `resolve_mkEntry_main` / `resolve_mkEntry_main_toList` — the bridge from the
  abstract `Store.resolve` to a concrete `List.take`/`List.drop` substring of the
  input, for a freshly minted main-arena entry.
* `reconstruct_two_sep` — the pure list core of the round-trip: splitting a list
  at two separator positions and re-joining with the separators is the identity.
* `segments_head_off` — the request-line span begins at input offset `0`.

## Safety vs. correctness, field by field

| Field                | Safety (`parse_wf`)            | Correctness (`parse_reqline_sound`) |
|----------------------|--------------------------------|-------------------------------------|
| method               | span in-bounds, resolves       | = `input[0, i₁)`, `i₁` = first SP   |
| target               | span in-bounds, resolves       | = `input[i₁+1, i₁+1+i₂)`, no inner SP |
| version              | span in-bounds, resolves       | = `input[i₁+1+i₂+1, L)`             |
| request line (whole) | —                              | serialize-of-parse = `input.take L` |
| header name (each)   | span in-bounds, resolves       | **UNCLOSED** (see below)            |
| header value (each)  | span in-bounds, resolves       | **UNCLOSED** (see below)            |

## UNCLOSED: the header-block round-trip

This file proves the request-line field extraction — the real soundness core.
It does **not** yet close the header-block round-trip. Specifically the following
are honestly **open** and are *not* proved anywhere:

* **Header value soundness.** That each resolved header value equals the exact
  OWS-trimmed input substring between the `:` and the line's CRLF (i.e. the
  meaning of the `parseHeaderLine` OWS-trim, not just its in-bounds span).
* **Header name canonicalisation soundness.** That each resolved canonical name
  equals the lowercase image of the exact input name bytes (the sidecar
  synthesis path in `canonNameEntry` is only shown to be *in-bounds*, not to
  denote the lowercased name).
* **Header-block serialisation.** That re-serialising the resolved header block
  with `":"` / OWS / CRLF reproduces the input head between the request line and
  the terminating `CRLFCRLF`.

For the headers, what holds today is only the **safety** result carried up from
`parse_wf`: their spans are in-bounds and `resolve` is total on them. The
meaning-level agreement above is future work. The request-line theorem is
structured (via `parseRequestLine_sound` + `resolve_mkEntry_main_toList` +
`reconstruct_two_sep`) so the same three-step recipe — field-extraction
soundness of the line parser, the `resolve`→substring bridge, and a
reconstruction lemma — applies directly to `parseHeaders` when that work is
picked up.

## Verification

* Builds clean under Lean 4 (project toolchain `leanprover/lean4:v4.17.0`):
  `lake env lean ArenaSound.lean` — zero errors, zero warnings, zero `sorry`,
  no unclosed goals.
* Registered as `lean_lib ArenaSound` in `lakefile.toml`; `lake build ArenaSound`
  succeeds.
* `#print axioms Arena.Parse.parse_reqline_sound` →
  `[propext, Classical.choice, Quot.sound]` — a subset of the permitted core
  axioms; no `sorryAx`, no added axioms.
