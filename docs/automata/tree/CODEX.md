# Cross-model audits of the tree statements

## Round 1 (gpt-6-astra, `codex exec --sandbox read-only`, 2026-11-06)

Brief: attack `canon_injective`, `corpus_absence` and the rest of `metatheory/Dregg2/Tree/`
(unicode normalization, duplicate keys, float canonicalization, empty-array/object aliasing, MMR
binding, zip truncation, vacuity). Twelve findings: six DEFECTs, three QUALIFICATIONs, three OK.
Codex built executable certificates to test several of them; the accepted ones are marked.

| # | tag | finding | adjudication |
|---|---|---|---|
| 1 | DEFECT | `enum` was checked only on strings; `{"enum":["Bash"]}` accepted `null` (an accepted certificate) | **fixed**: `scalarOk` refuses every non-string when `enum` is present, and the compiled `hfinal` carries the same conjunct; `compile_correct` re-proved; `Pins.lean` pins `null`, `[]` refused |
| 2 | DEFECT | explicit `type: []` / `anyOf: []` read as absent; dangling `items: 999`; extra wrapper keys | **fixed**: explicit empty `type`/`enum`/`allOf`/`anyOf` refused; `Schema.ok` checks every child reference; wrapper and table readers refuse unknown keys; pinned |
| 3 | DEFECT | `dec 1 (-2^64-1)` passed `WF`; its tag-4 exponent is a bignum, which RFC 8949 §3.4.4 forbids (an accepted certificate) | **fixed**: `WF` adds `expOk` (exponent ≥ `-2^64`); pinned both sides of the boundary; GROUNDING §3.1 corrected (bignum integers are supported, the earlier "below 2^64" line was wrong) |
| 4 | OK | no canonical-byte alias: `1.0 = 1 = 10e-1`, `-0 = 0`, `1e400`, the `2^64` boundary, leading-zero and small bignums refused, escape-decoded duplicates refused, `[]`/`{}` = `80`/`a0` | — |
| 5 | QUALIFICATION | `wf_unique` is one level over identical entries; "each JSON value has one tree" exceeded the theorems | **docstrings corrected** (`Value.canon_injective`, `Spec` header, renamed `wf_unique_obj`). The recursive two-spellings property of `Json.parse` is pinned by `#guard`, not proved; open |
| 6 | OK | Merkle collisions pinned and substantive; wrong path, sibling swap, false absence, arr/obj confusion all need a named collision | — |
| 7 | QUALIFICATION | openings bind a structural tree; they do not show the committed record is canonical, or that a complete tree exists behind an opaque root | stated in `FORMAT.md` and the demo README: canonicality of the named corpus is the projection's, which `tree-check project` recomputes; the schema certificate (full disclosure) does check `WF` |
| 8 | OK | no collision-free false zero; the zip truncation in `matchesQ` is unreachable because accepted receipts have equal lengths; an empty query matches everything | — |
| 9 | DEFECT | root lengths unchecked: roots `""`, `"00"`, `"0000"` share one MMR leaf (`leafOf` drops leading zeros); `corpus_absence` took `hrlen` as a premise | **fixed**: `corpusCheck` requires every record root to be 32 bytes; `corpus_absence` derives it from acceptance |
| 10 | DEFECT | `mmrHash_coll` and `shakeH_len` were cited and did not exist | **fixed**: hashes are `fix32` of SHAKE256 (the identity on its 32-byte output, pinned), `shakeH_len`, `shakeH_coll`, `Spec.mmrHash_coll` (an MMR-hash collision at two lists of ≤ 2 naturals below `2^256` is a SHAKE256 collision at two distinct framed inputs), `corpus_absence_shake` at the executable's hashes |
| 11 | QUALIFICATION | the schema language is a dialect (no `const`, no `$ref` keyword, integer bounds only, whole-string patterns); nothing ties tables to shell behaviour | GROUNDING §3.2 now says exactly that; the demo states the pattern's meaning (bytes of the decoded leaf, no shell parsing) |
| 12 | DEFECT | `checkRun_annotate` (completeness) was advertised and did not exist | **docstring corrected**: completeness is not proved; the producer's runs are accepted by `tree-check` |

Round 2 runs after the demo lands, against the corpus certificate and the microsite's claims.
