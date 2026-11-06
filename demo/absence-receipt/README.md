# Absence receipt: 100,000 public documents, zero secrets, one signed sentence

Demo (a) of the automata program (`docs/automata/SUBSTRATE-DECISION.md` §5 item 1, §7 row D),
2026-11-06. Tags: [MEASURED] a run on the Mac (Apple M2 Max, other lanes running) today; [READ]
seen in the cited file; [INFERRED] derived here.

The receipt says, and is signed over:

```
{"v":"absence-receipt-v1",
 "policy_blake3":"984aba5f…",      the policy source below
 "table_blake3":"7434e218…",       the absence automaton the policy compiled to
 "corpus_mmr_root":"17d69bbf…",    the 100,000 documents, in order
 "corpus_pin":"681f94fc…",         crates.io-index commit they came from
 "n":100000,
 "count":0}                        documents the automaton rejects
```

The full body is `receipt.json`; its signature is `receipt.json.sig`; the signer is `allowed_signers`.

## The legs, and which is which

| leg | what runs | what it establishes | status |
|---|---|---|---|
| corpus | the first 100,000 index files of `rust-lang/crates.io-index` at `681f94fc638e5a7639aa410c34b984a12bcd8dfe`, paths sorted bytewise (dot-entries and the root `config.json` skipped); one document = one file's bytes | a public, reproducible input | public data only |
| commitment | `dregg-query`'s `Mmr<Blake3Mmr>` (`dregg-query/src/mmr.rs`, tags `dregg-query-mmr-v1:{leaf,node,bag,empty}`) over leaf values `blake3(document)` | `corpus_mmr_root`; the 100,000 hashes are checked in (`documents.tsv.gz`), so the root recomputes without the clone | Rust, the dregg-query mirror of `Dregg2.Lightclient.MMR` |
| policy → table | `policy.txt` compiled by `absence-receipt compile`: `~(any* · (P1 \| P2) · any*)` through `dregg_dfa::Re::compile` (derivatives over the crate's ACI canonical form), then `dregg_dfa::Dfa::minimize` | `absence-table.json`, 129 states | the table is produced by `dregg_dfa::Re::compile`, which is differential-tested, not proved: `demo/absence-receipt/tests/differential.rs` checks it against the former interim compiler (frozen there) and a hand-written scanner for the two patterns, on the controls and 10,000 seeded random strings. No Lean decider is in that loop; the Lean runner only executes the table. The policy grammar is still a second grammar outside Lean; lane B's `policyc compile --absence` is meant to replace it |
| verdicts | `lake exe dfa-run absence-table.json --corpus …` (Lean, compiled) | `count`, from re-executing the table on every byte of every document | the verdict function is `TableRun.acceptsBytes`; `metatheory/Dregg2/Automata/TableRunSpec.lean` proves it is `Deriv.PredRE.TableDfa.accepts` on the document's bytes (`accepts_iff`), and `rejectCount_eq_zero_iff` says what `count = 0` means |
| cross-check | `absence-receipt count` (Rust `dregg_dfa::Dfa::matches`) | the same count from the runtime crate | must agree; `run.sh` stops if it does not |
| served-path evidence | one record, document 1598 (`3/c/cxr`, 2048 bytes), its run emitted by Lean as a `DfaRoutingTableEmit.tableRoutingDesc` descriptor and proved by the v2 assembly | the served table-routing family proves and verifies a real record's run, and refuses a wrong final state | `circuit/tests/absence_receipt_record.rs` |
| receipt | `absence-receipt receipt`, then `ssh-keygen -Y sign` (ed25519, namespace `absence-receipt`) | a signed body naming policy, table, corpus, `n`, `count` | the private key is under `keys/`, gitignored, never committed |

Document 1598 is the first document whose length is a power of two: the v2 assembly requires a
power-of-two trace height ("base trace height 1724 must be a power of two" for document 0
[MEASURED]) and an exact-public table pins the height to the run length.

## Counts [MEASURED]

| quantity | value |
|---|---:|
| index files at the pin | 371,277 |
| documents | 100,000 (`1/a` … `er/rn/errno-codes`) |
| bytes | 1,770,996,081 |
| MMR leaves / nodes / peaks | 100,000 / 199,994 / 6 |
| policy patterns | 2 (`AKIA[0-9A-Z]{16}`, `-----BEGIN [A-Z ]*PRIVATE KEY-----`) |
| absence DFA before / after minimization | 4,577 / 129 states (128 accepting; state 0 is the dead sink, entered on a match); the former interim compiler: 9,153 / 129, the identical minimized table |
| table | 33,024 transitions, 71,179 bytes of JSON |
| run rows, whole corpus (one per byte) | 1,770,996,081 |
| documents rejected (`count`), Lean and Rust | 0 and 0 |
| controls (`controls/`, plus a PEM header written by `run.sh`) | AWS example key: REJECT; PEM header: REJECT; 19-character near miss: ACCEPT |
| the one STARK: rows / width / constraints / tables / batch instances | 2,048 / 3 / 4 / 1 / 2 |
| the one STARK: prove / verify / proof size | 724.0 ms / 15.7 ms / 90,714 bytes (postcard) |

## Wall clocks [MEASURED, `run.sh`, Mac]

Two runs: the first (2026-11-06, interim compiler) and the re-run after the table moved to the
`dfa` crate (same day, other lanes running). The re-run reproduced every checked-in artifact byte
for byte: table, `dfa-run.json`, `mmr.json`, record descriptor, receipt body, and signature
(ed25519 signatures are deterministic).

| leg | first run, s | re-run, s |
|---|---:|---:|
| select (walk 371,277 files, sort, take 100,000) | 9.3 | 14.3 |
| hash 100,000 documents (blake3) | 36.4 | 46.6 |
| MMR root | 0.1 | 0.2 |
| compile the table (interim compiler, then `dregg_dfa`) | 42.4 | 2.7 |
| `dfa-run` over 1.77 GB (Lean, native) | 48.3 | 57.8 |
| Rust cross-check count | 30.1 | 41.9 |
| emit the record descriptor (`lake env lean --run`, interpreted) | 11.4 | 27.5 |
| receipt, sign, verify | 0.3 | 0.3 |
| the STARK (one record), prove + verify | 0.74 | not re-run |

Both scans look I/O-bound [INFERRED]: the user CPU of `dfa-run` was 10.7 s of its 45-48 s wall.

## Commands

```
# the corpus (untrusted data: clone into a fresh empty directory; nothing in it is executed)
git init idx && cd idx
git remote add origin https://github.com/rust-lang/crates.io-index.git
git fetch --depth 1 origin 681f94fc638e5a7639aa410c34b984a12bcd8dfe && git checkout FETCH_HEAD

# everything, timed (needs the clone)
INDEX=/path/to/idx demo/absence-receipt/run.sh

# a stranger's check, no clone: signature, corpus root from the hash list, policy and table digests
demo/absence-receipt/run.sh verify

# the Lean pieces
cd metatheory
lake build dfa-run && ./.lake/build/bin/dfa-run ../demo/absence-receipt/absence-table.json ../demo/absence-receipt/controls/aws-key.txt
lake env lean Dregg2/Automata/TableRunSpec.lean          # the theorems; or scripts/automata-check.sh

# the one STARK
cargo test -p dregg-circuit --release --test absence_receipt_record -- --nocapture
```

## What is NOT claimed

- **No STARK over the corpus.** The 100,000 verdicts are native re-execution of the table by the
  Lean runner; verifying them means re-running it. One record is proved under the served family,
  as evidence that the served path accepts a real record, not as a proof about the corpus.
- **The table is not proved to be the policy's absence automaton.** `dregg_dfa::Re::compile` is
  Rust and unproved; its ACI normalizer is not proved to meet Lean's similarity. `TableRunSpec`
  proves the runner computes `TableDfa.accepts` for whatever table it is given; that the table denotes "contains neither pattern" is the compiler's obligation
  (`tableDfa_faithful`'s agreement premise for a Lean-compiled table). The controls are evidence,
  not proof.
- **No non-omission certificate beyond the root.** The MMR root commits to these 100,000 hashes in
  this order. That they are the first 100,000 files of the pinned commit is checked by re-running
  `select` against a clone, not by a proof.
- **`count` is the runner's count, not a Datalog `Count`.** Lane A's `datalog-check` is not wired
  in; feeding it a `match(i)` relation produced by this same runner would add nothing.
- **The proved record's word is public** (an exact-public table carries the run); it says nothing
  private and does not bind the record to the MMR leaf. The route-commitment conjunct is the
  program's open milestone (SUBSTRATE-DECISION §5 item 2).
- The signature names a demo key, not a person or an organization.

## What the interim compiler found, and the fix

`dregg_dfa::Re::compile` did not finish on `~(any* · AKIA · any*)` within 60 s (one pattern, four
literal bytes; a two-pattern run reached 4.5 GB of memory before it was stopped) [MEASURED]. Its
smart constructor `Re::or` normalized commutativity and idempotence of the top pair only, with no
associativity, so the derivatives of `any* · w` grew as differently nested alternations and never
repeated; Brzozowski's finiteness holds only up to ACI similarity (`metatheory/Dregg2/Crypto/Deriv/Similarity.lean`,
`metatheory/Dregg2/Crypto/Deriv/Finiteness.lean`'s `der_finite`). The demo first worked around it with its own normalizer
(9,153 states, 129 minimized, 42.4 s). The crate's smart constructors now keep an ACI canonical form
(the invariant is documented on `enum Re` in `dfa/src/derivative.rs`), the crate gained `Dfa::minimize`,
and the demo's workaround is gone: the crate reaches 4,577 states, minimizes to the same 129-state
table byte for byte, and `demo/absence-receipt/tests/differential.rs` keeps the former compiler as its differential partner:

```
cargo test --manifest-path demo/absence-receipt/Cargo.toml --release --test differential
```
