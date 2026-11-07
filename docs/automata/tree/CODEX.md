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

## Round 2 (two reviewers, 2026-11-06)

Both ran on the same code and demo: codex `gpt-6-astra` (`codex exec --sandbox read-only`; it was
not withheld this time), and an independent Claude Opus review, briefed with only the code paths
and the attack questions, not round 1's conclusions. Codex builds certificates and runs
`tree-check` on them, and so did the Opus reviewer (its attack files are listed in the lane's
transcript). **Neither found a certificate `tree-check` accepts with a wrong count for the
committed corpus without a hash collision.** Both independently found the same three public-claim
defects (disclosure, the lost `\u0070` escape, execution wording).

| finding (reviewer) | tag | adjudication |
|---|---|---|
| printed paths joined with "/" made the one-step key `"input/command"` print like the two-step path; the reviewer had an accepted certificate printing `count: 0` over the real root with A's table (Opus 1) | BLOCKER (the printed statement, not the theorem) | **fixed**: `tree-check` prints paths as JSON arrays of `{"key"}`/`{"key_hex"}`/`{"idx"}` steps; the attack file now prints `[{"key": "input/command"}]` |
| "no other field is disclosed" is false: sibling keys appear in clear, sibling values sit behind unsalted digests (`digest("Bash")` recovers `name`), equal digests link records, and the checker accepts `here` at any level (Opus 2, codex 5) | DEFECT | **wording fixed** (README, microsite list what an opening discloses); minimal disclosure is the producer's choice, not the checker's. Salted leaf digests are the repair to make, not made |
| the escaped control printed unescaped on both pages and in `Value.lean` (an authoring tool decoded `\u0070`) (Opus 3, codex 7) | DEFECT | **fixed**, now written with a literal backslash; flat-scan populations separated (47 of 3,382 real lines, 48 of 3,384 with controls) |
| counts other than 0 had no theorem against the committed MMR root (Opus 4, codex 9) | DEFECT | **fixed**: `Spec.corpus_count_mmr` (any count) |
| the MMR collision is a collision of `mmrHash`; `mmrHash_coll` lifts it to SHAKE256 only for lists of ≤ 2 naturals below `2^256`, and nothing shows `mrootFind`'s pair meets that (Opus 5, codex 9) | QUALIFICATION | **stated** in README and microsite; the bound on `mrootFind` pairs is open |
| Python `json.loads` sits before the projection: last-wins duplicates, float round trip (Opus 6, codex 4) | DEFECT | **producer lane**: `project_records.py` refuses duplicate keys and keeps numeric tokens exact (see summary.json) |
| the count-0 claim read as "no agent ran `pkill -f`"; "none runs it" is a human reading (Opus 7, codex 6) | DEFECT | **wording fixed**: the scope sentence sits beside the zero on both pages; human readings tagged [READ]; the `Monitor` tool's shell commands are named as outside `name = Bash` |
| a statement root of 34 bytes was accepted and echoed padded (Opus 8) | DEFECT | **fixed**: statement digests must be exactly 32 bytes |
| duplicate keys in the certificate envelope (Opus 9, codex 3); more than one constructor or unknown fields in an opening (codex 3) | DEFECT | **fixed**: the envelope must pass the strict `Json.parse`; opening and evidence objects must carry exactly their constructor's fields |
| Keccak counters covered only the openings; the published field certificate is 88, not 3 (codex 8) | DEFECT | **fixed**: `tree-check` prints `keccak_f_openings`, `_table(s)`, `_mmr` and `_total`; the MMR count is labelled as computed by formula (`2n + 1`, one block each) |
| `Spec.lean`/`Pins.lean` are in no lake target (Opus 10) | QUALIFICATION | they are in `automata-check.sh`'s family list (`Dregg2/Tree/`), which is the gate; `lake build tree-check` does not check them |
| the Layer B′ half of `field_accept_bound` holds by definition; the empty-string branch is separate (Opus 11, codex 9) | QUALIFICATION | **stated**: the content is the `DfaAccepts` run; the private-leaf composition (the DFA leg over a digest-only leaf) is the next leg |
| the projection refuses `1e4097` but accepts `10e4096` (Opus 12) | QUALIFICATION | the cap is on the written exponent, as `Json.lean` says; values are never aliased |
| the Rust schema producer missed round-1 repairs (codex 2) | DEFECT | **producer lane**, ported with agreeing negatives |
| `run.sh` did not assert verdicts (codex 13) | DEFECT | **producer lane**: honest = 0, tampered = 1, anything else fails the run |
| JCS: the integers coincide after the binary64 conversion, not as two JCS numbers (codex 11) | QUALIFICATION | **wording fixed** on the microsite |
| strangers can re-verify one field certificate; the corpus counts are local measurements while the full certificates stay unpublished (codex 12) | QUALIFICATION | **stated** on both pages |
| Q1/Q2/Q3/Q4 attacks (canonical aliases, pinned collisions, short/long `full`, reordered conjuncts, duplicated records, empty query, schema keywords) (both) | OK | — |
