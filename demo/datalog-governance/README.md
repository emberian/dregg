# Demo (b): a governance question over an agent session forest, as a stratified Datalog certificate

Lane A of `docs/automata/SUBSTRATE-DECISION.md` §7, 2026-11-06. Tags: [MEASURED] a run on ember's
Mac (Apple silicon) on that day; [READ] seen in a file.

## The default run is synthetic

`./run.sh` runs on a SYNTHETIC forest by default. `synth_transcript.py` (seeded, deterministic)
writes a projection in the same shape as the real one: a root and three sub-agents in a depth-2
tree (three spawns), about 190 tool calls of Read / Edit / Write / Bash / Agent, all over invented
paths in a fictitious project `/home/demo/acme-ledger/`. No field comes from a real session. There
are two variants, with the same program:

| variant | what differs | EDB facts | stratum 0 / 1 firings | count(violation) | verifyJ | EDB root |
|---|---|---|---|---|---|---|
| `data/synthetic/violating/` | `lane-b` edits `src/ledger/rounding.py` unseen (one `blind_edit`); `lane-c` writes `/etc/hosts` (one `forbidden_write`) | 550 | 412 / 4 | **2** | 0.70 s | `0xadd345fa…6b8327` |
| `data/synthetic/fixed/` | `lane-b` reads the file first; `lane-c` writes in the project | 557 | 416 / 0 | **0** | 0.57 s | `0x20f64ad4…f1227d` |

[MEASURED]: both are accepted, each with its own signed receipt. On the fixed certificate,
`open-lower` (claims 6), `wrong-count` and `dropped-fact` are refused, and the weaker checker
accepts `open-lower`. Both variants also exercise the allowed paths: an edit after the agent's own
read, an edit after its own earlier write, and an edit of a file the parent read before the spawn.

The real-session run below exists. Its artifacts (`data/transcript.json` and everything derived
from it directly under `data/`) are session-derived and under ember's decision. `./run.sh --real`
re-runs it from the local file without re-exporting; `REAL_OUT=<dir>` sends its outputs elsewhere.

## The question (the real-session run)

The session is `e3ba49ed-a526-4ecd-8807-58b73757aaca`, a completed Claude Code session in
`~/dev/aidev`. With its 72 sub-agents it is 73 transcripts and 3,382 tool calls. The question,
in `program.json`:

> Did any **sub-agent** `Edit` a file that neither it (earlier) nor its parent (before spawning
> it) had read or written? Did any sub-agent write under a forbidden directory (`~/.ssh/`,
> `~/hellas/`, `~/dev/nanodregg/`, `~/.claude/projects/`, `~/Library/`, `/etc/`)?

```
written_path(P)    :- writes(W, P).
touched(R, P)      :- reads(R, P).
touched(R, P)      :- writes(R, P).
touch_upto(A, P, S)  :- touched(R, P), tool_call(R, A, T, S), written_path(P).
touch_upto(A, P, S2) :- touch_upto(A, P, S1), next(A, S1, S2).
prior_touch(W) :- edits(W, P), tool_call(W, A, T, S), next(A, S0, S), touch_upto(A, P, S0).
prior_touch(W) :- edits(W, P), tool_call(W, A, T, S), spawned(A, Q, K), next(Q, K0, K), touch_upto(Q, P, K0).
--- stratum 1 ---
blind_edit(W)      :- edits(W, P), tool_call(W, A, T, S), spawned(A, Q, K), not prior_touch(W).
forbidden_write(W) :- writes(W, P), tool_call(W, A, T, S), spawned(A, Q, K), prefix_of(P, X), forbidden_prefix(X).
violation(W) :- blind_edit(W).
violation(W) :- forbidden_write(W).
```

The statement is `count(violation) = 0` [MEASURED]. This is the Count = 0 (absence) shape. All 12
sub-agent edits had an earlier touch, and no sub-agent wrote under a forbidden directory.

**Where the brief's question changed, and why.** The brief asked "every path a sub-agent wrote was
read earlier". Run literally, that flags all 78 of the 78 sub-agent writes. The first version of
the program, checked and accepted, counted 84: those 78 plus the root's own 6 memory writes under
`~/.claude/projects/` [MEASURED]. The sub-agent writes are mostly `Write` calls that
CREATE new files, and the 12 `Edit`s follow the agent's own `Write`. The projected transcript cannot
tell a creation from a blind overwrite. The refined question counts modifications (`Edit`,
`MultiEdit`, `NotebookEdit`). It counts an earlier write as well as a read as "having seen the
file". It applies the forbidden-directory leg to sub-agents only, because the root's six writes
under `~/.claude/projects/` are its own memory files.

## What is proved, and what is not

Proved [READ `metatheory/Dregg2/Datalog/`]: when `datalog-check` accepts, `JoinClosure.verifyJ`
returned `true`. `verifyJ_verifyS` makes that `StratifiedCert.verifyS = true`. `verifyS_sound` then
says the checked database is EXACTLY the stratified model of this program over this EDB, and its
count of `violation` is the claimed count. `verifyS_strata_exact` says the same per stratum.
`SafeCoincidence.verifyJ_receipt` bundles it all for what the executable accepts: the root, the
database being EXACTLY the standard (unrestricted) stratified model, the count, and that same
database being a supported model. `verifyS_count_zero_absent` turns count 0 into "no `violation`
fact is in the model". By `countS_unique_or_collides`, different accepted counts for one
`(program, strata, root, pred)` require a collision of the instantiated list hash. Reducing that to
a SHAKE256 collision additionally requires injectivity of the byte encoding (checked on examples,
not proved). The same obligation holds for the program digest.

Not proved, or not claimed:
- **The scope of the zero.** Zero violations in the extracted REQUEST log, under lexical path
  identity and resolved spawn relationships. This does not establish successful prior access,
  filesystem-resolved forbidden-path exclusion, complete agent coverage, or authenticated
  correspondence to the original session or export. Facts are tool requests, with no check that a
  call succeeded. Paths are compared as strings, with no symlinks, `..` or case folding. The
  sub-agent rules need a resolved `spawned` fact. The export sha256s in the projection's metadata
  are not in the EDB.
- **No proof system.** Verification is native re-execution of the extracted checker. There is no
  STARK and no succinctness.
- **The extractor is trusted.** That covers `project_transcript.py` (which calls count as file tools
  and how agent ids are read from `Agent` results) and `extract_edb.py` (`next` is consecutive
  per-agent steps; `prefix_of` is every ancestor directory). The EDB carries `name(id, utf8)` facts,
  so the root binds what each id means, and both scripts are short enough to audit.
- **Only the structured file tools are seen.** A `Bash` command that writes a file (`>`, `sed -i`,
  `git`) is invisible to this question.
- **Parents are ordered by spawn step.** A parent's touch counts only if it came before the
  `Agent` call that spawned the child. Order across agents is not otherwise modelled.
- **Count is a set count.** Every event fact carries its occurrence id, so two identical calls stay
  two facts (codex round 3, finding 5).
- **The hash.** SHAKE256 with a domain prefix over a canonical framed encoding stands in for the
  deployed cSHAKE leaf root. Injectivity of the byte encoding is checked by round-trip `#guard`s in
  `DatalogCheck.lean`, not proved.
- **The transcript.** `data/transcript.json` is a PROJECTION of the redacted
  `cv export --format json --redact` of the root and of each `agent-<id>`. It keeps tool name, file
  path, ids and order, and drops every message text and tool output. The full redacted exports are
  106 MB; their sha256s are recorded in the projection.

## Counts [MEASURED]

| quantity | value |
|---|---|
| transcripts / tool calls | 73 / 3,382 |
| EDB facts | 8,839: tool_call 3,382, next 3,309, reads 783, name 678, prefix_of 498, writes 88, spawned 83, edits 12, forbidden_prefix 6 |
| flattened EDB (MMR leaves) | 45,506 integers |
| active domain | 4,738 distinct constants |
| stratum 0 | 176 rounds, 3,974 firings |
| stratum 1 | 0 firings |
| final database | 12,813 facts; `count(violation) = 0` |
| closure join candidates per rule (stratum 0, rules 0-6) | 88, 783, 88, 92, 2,942, 12, 0 |
| closure join candidates per rule (stratum 1, rules 7-10) | 12, 0, 0, 0 |
| closure by enumeration, for comparison | `4738^8` substitutions for rule 6 alone: not runnable, which is why `JoinClosure` exists |

| wall clock | value |
|---|---|
| extract (`extract_edb.py`) | 0.09 s |
| prove (`prove.py`, semi-naive, logs firings) | 1.9-2.3 s |
| check: `verifyJ` alone, as printed by the checker | 13.5-26.0 s across four runs (the Mac was shared with other lanes) |
| check: whole process, including counts and diagnostics | 26-47 s |
| verify the receipt signature (`ssh-keygen -Y verify`) | 0.014-0.016 s |
| `lake build datalog-check`, first build | 2 min 53 s |

Falsifiers, run by `run.sh` on this data [MEASURED]:

| certificate | `datalog-check` | weaker checker |
|---|---|---|
| `open-lower`: stratum 0 without its `prior_touch` firings, so all 12 edits come out "blind" and the claim is 12 | REFUSE (stratum 0: NOT CLOSED) | `--weaker-no-lower-closure` (closure at the top stratum only): **ACCEPT** |
| `wrong-count`: the honest certificate claiming 1 | REFUSE (count differs) | n/a |
| `dropped-fact`: one `reads` fact deleted, statement root kept | REFUSE (root differs; replay refused a firing) | n/a |

## Commands

```
cd demo/datalog-governance
./run.sh                       # synthetic: both variants, receipts, falsifiers (the default)
./run.sh --real                # the real-session run from the local data/transcript.json
REAL_OUT=/tmp/x ./run.sh --real  # the same, with its outputs written elsewhere
```

Check a checked-in certificate and receipt without running anything else (synthetic fixed shown;
`data/synthetic/violating/` and `data/` work the same way):

```
cd metatheory && lake build datalog-check
./.lake/build/bin/datalog-check ../demo/datalog-governance/data/synthetic/fixed/certificate.json
cd ../demo/datalog-governance
ssh-keygen -Y verify -f allowed_signers -I datalog-governance@dregg -n dregg-datalog-receipt \
  -s data/synthetic/fixed/receipt.txt.sig < data/synthetic/fixed/receipt.txt
```

The receipt signs `(program_digest, root, pred, count)` as the checker printed them. Verifying the
signature authenticates that body under the demo key only. It attests neither the checker binary
nor the source data. To verify the computational claim, re-run `datalog-check` on the certificate
and compare every field of its output (program digest, root, pred, count, verdict ACCEPT) with
the signed body. The private key
lives in `keys/`, which git ignores. Running `run.sh` without that directory makes a new key and
rewrites `allowed_signers`.

Files: `program.json` (rules, strata, policy), `synth_transcript.py`, `project_transcript.py`, `extract_edb.py`,
`prove.py`, `forge.py`, `run.sh`, `allowed_signers`. Under `data/`: `transcript.json`, `edb.json`,
`certificate.json` (the checker's input: statement and certificate), `check.out`, `receipt.txt`,
`receipt.txt.sig`.
