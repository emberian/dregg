# Tree certificates over a real agent session: what the Bash calls said about `pkill -f`

Initiative 12 (`docs/automata/tree/GROUNDING.md`), 2026-11-06. Tags: [MEASURED] a run on ember's
Mac (Apple silicon, other lanes running); [READ] seen in a file. Counts over clocks.

## The corpus

Session `e3ba49ed-a526-4ecd-8807-58b73757aaca` (`~/dev/aidev`, the session demo (b) used): the root
and its 72 sub-agents, exported with `cv export <id> --format json --redact --frozen`, every
`tool_use` projected to one record `{"name": <tool>, "input": <input object>}` in transcript order
(root, then sub-agents sorted by id). **3,382 records, 2,376 of them Bash** [MEASURED]. Each record
is projected to the canonical tree (`Dregg2.Tree.Json.parse`: escapes decoded, duplicate keys
refused, exact numbers, keys in RFC 8949 §4.2.1 order) and committed by its Merkle root; the
corpus is the MMR of the 3,382 roots, `219ace22…4a61` (with the two controls appended: `f5a8ab30…2298`).
The Rust projection (`tree-cert project`) agrees with Lean's `tree-check project` on all 3,382
records and 60 edge cases (28 accepted, 32 refused), byte for byte [MEASURED].

## Three questions, three certificates, one root

A record MATCHES a query when `name` is exactly `Bash` and `input.command` is a string the second
table accepts. The certificate's per-record evidence is a path opening: a non-Bash record opens
`name`; a Bash record opens `input.command`. **What an opening discloses** (review round 2): the
opened leaf in full; the KEYS of every object on the path (e.g. that an `input` has `description`
and `timeout`); and SHAKE256 digests of every sibling value. The digests are unsalted, so a guessable
sibling value is recoverable by hashing guesses (`digest("Bash")` is the `name` digest of all 2,376
Bash records, `120000` a `timeout`), and equal digests link records. A matching record discloses
both queried fields. Minimal disclosure is this producer's choice; the checker also accepts an
opening that discloses a whole subtree. Salted leaf digests are the open repair.

| | query (table for `input.command`) | real | + 2 controls | refuted at `name` / at `command` |
|---|---|---:|---:|---|
| A | contains `pkill -f` (`tables/pkill.json`, dregg-dfa, 10 states) | **13** | 15 | 1,006 / 2,363 |
| B | `pkill … -…f` at command position: after start, newline, `; & \| ( $(` or a backtick, optionally behind `sudo env xargs nohup exec command time timeout N` (`tables/invocation.json`, 43 states) | **7** | 9 | 1,006 / 2,369 |
| C | B without the backtick boundary (`tables/invocation-nobacktick.json`, 43 states) | **0** | 2 | 1,006 / 2,376 |

**A is 13, not 0, and 13 is correct.** All thirteen are Bash commands that *mention* `pkill -f`:
heredocs quoting the 2026-10-10 incident, `rg` searches for it, quoted house rules. None of them
invokes it [READ: a human reading of the thirteen commands, not a theorem].
**B's seven** are the same kind: markdown code spans (`` `pkill -f "cat" -u ember` ``) inside heredoc
prose, which the backtick boundary reads as command substitution. **C is the absence receipt:
Count = 0** over the 3,382 records, with B's limits plus one more (a `` `pkill -f x` ``
substitution is missed), written in `query-invocation.policy`. **C = 0 means no `Bash` call's
`input.command` in this redacted export matches this byte pattern. It is not evidence that no
process was killed by pattern**: shell commands in other tools (two `Monitor` calls carry one)
are outside `name = Bash`, and `cv --redact` could in principle have removed a match. No shell parsing happens anywhere:
the claim is about bytes of the decoded leaf, and its scope is exactly the pattern. The misses
(`bash -c '…'`, aliases, `kill $(pgrep -f …)`, `pkill --full`, `pkill -u x -f`, `env FOO=1 …`) and
the over-counts (a heredoc line that starts with `pkill -f`) are listed there.

The controls are `{"name":"Bash","input":{"command":"\u0070kill -f node"}}` (escaped) and the plain
spelling. Both match under A, B and C. **A flat byte scan of the raw JSON lines for `pkill -f`
hits 47 of the 3,382 real lines (48 of 3,384 with the controls) and misses the escaped control**
[MEASURED]; the tree certificate reads the decoded leaf and does not. The other direction matters
too: of the 47 real hits, 34 are not Bash commands (32 Agent prompts, 2 Writes).

Tables: `Bash` (exact) from Lean `policyc` (`tables/bash.policyc.json`). The three command tables
from `dregg_dfa::Re::compile` + `Dfa::minimize` (`src/invocation.rs`; policyc did not finish
compiling `.* … .*` within 15 minutes). A's table is checked equal to the complement of policyc's
`--absence` table (`tables/equiv.py`, 9 reachable state pairs); B's and C's against a `regex`
oracle on all 2,378 Bash commands and 36 hand cases, zero disagreements [MEASURED]. That is
regression evidence, not a proof that the tables denote the patterns.

## What is proved

`tree-check verify` is the Lean function `Dregg2.Tree.corpusCheck` at SHAKE256 node, flat and MMR
hashes (`metatheory/TreeCheck.lean`). Rust produces the certificates and never decides one.

- `Spec.corpus_absence_shake` (count 0) and `Spec.corpus_count_mmr` (any count): if
  `tree-check` accepts a corpus certificate, then for ANY admitted records whose Merkle roots'
  MMR root is the statement's, and the tables the statement commits to, exactly `count` records
  match; or a hash collides at a pair the theorem computes: the MMR hash at the pair `mrootFind`
  names, the node hash inside some record's opening at the pair `walkFind` names, or the flat
  hash at two table encodings. The node and flat collisions are SHAKE256 collisions at distinct
  inputs (`shakeH_coll`); the MMR collision is lifted to SHAKE256 by `mmrHash_coll` for lists of at
  most two naturals below `2^256`, and that `mrootFind`'s pair has that shape is not yet proved.
- `walk_sound`: an accepted opening reports the record's true value at the path (or its
  absence), or a named collision. `canon_injective`, `ofCanonicalBytes_sound`: every value inside
  a certificate is the canonical CBOR of exactly one tree.
- `field_accept_bound`: an `accept` at a non-empty string leaf is a `Dfa.lean` accepting run
  reading exactly the leaf's bytes (the content commitment there is the leaf's own digest, by
  definition; the private-leaf composition is the next leg).

Not proved, not claimed: that the projection maps two spellings of one JSON value to one tree (it
is pinned by `#guard`s); that the export reached the projection intact (`project_records.py`
loads the cv export with Python's `json`, refusing duplicate keys and keeping every number's
source token: 0 duplicates and 599 numbers, all integers, in this corpus); that the tables denote the patterns (differential tests); that the cv
export is the session (the export sha256s are in `summary.json`; R0-R3 of initiative 10 is where
that is earned); anything about what a shell would execute.

## Counts [`tree-check verify`; wall clocks MEASURED on the Mac with other lanes running]

| certificate | records | frames hashed | frame bytes | Keccak-f: openings + tables + MMR = total | nodes disclosed | wall |
|---|---:|---:|---:|---:|---:|---:|
| C, real | 3,382 | 9,140 | 4,487,457 | 37,828 + 97 + 6,765 = **44,690** | 3,382 | 12.8 s |
| one record, `field-cert-2580-c.json` | 1 | 3 | 184 | 3 + 85 + 0 = **88** | 1 | < 0.1 s |

Openings are counted as the checker hashes them; the table and MMR terms are computed by formula
(`keccakFOf(19 + |encode table|)`; one block per MMR hash, `2n + 1` hashes). Per record: 2.7
frames and 11.2 opening Keccak-f. Frame bytes are dominated by the disclosed Bash commands. All 18
tampered copies (count ±1, two records swapped, a record dropped, a refutation opened at the wrong
path, the two table digests swapped; for each of A, B and C) exit 1, and `run.sh` fails on any
other exit code.

## Re-verify

```
cd metatheory && lake build tree-check
./.lake/build/bin/tree-check verify ../demo/tree-absence/field-cert-2580-c.json     # ACCEPT
./run.sh        # from demo/tree-absence: export, project, tables, conformance, all certificates
```

**What a stranger can recheck today:** the one-record certificate below, and the Lean theorems.
The corpus counts are locally verified measurements until the full certificates are published.
`field-cert-2580-c.json` opens one record (`cv recipes 2>&1 | head -80; cv schema 2>&1 | head -80`)
at `input.command` against C's table: verdict `reject`. Its root is in `summary.json`.

**Not in git, by decision pending with ember** (INITIATIVES decision 1): `corpus/` and the three
full certificates. They disclose every Bash command of the session (redacted by cv). The
statements, roots, counts and the one-record certificate are here; `run.sh` regenerates the rest.
