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

An earlier run over a real Claude Code session (73 transcripts, 3,382 tool calls) was removed
from the repository on 2026-11-07: session-derived data does not belong in a public repo. Its
projection script `project_transcript.py` stays, for local use only; nothing it writes is committed.

## The question

In `program.json`: did any **sub-agent** `Edit` a file that neither it (earlier) nor its parent
(before spawning it) had read or written? Did any sub-agent write under a forbidden directory?
Modifications (`Edit`, `MultiEdit`, `NotebookEdit`) are counted, an earlier write counts as having
seen the file, and the forbidden-directory leg applies to sub-agents only.

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
- **The transcript.** The synthetic `data/synthetic/*/transcript.json` files are generated by
  `synth_transcript.py` in the shape `project_transcript.py` produces: tool name, file path, ids and
  order, no message text or tool output.

## Commands

```sh
# From the repository root, with Python 3, OpenSSH (-Y), and the pinned Lean toolchain:
demo/datalog-governance/run.sh         # regenerate both synthetic variants; verify; falsify
demo/datalog-governance/run.sh verify  # verify the two original certificates and signatures
WORK=/fresh/output demo/datalog-governance/run.sh # retain outputs in an empty directory
```

The script bootstraps `datalog-check` if its executable is missing. Every synthetic rerun goes to
an empty output directory (a new temporary directory by default). It compares the regenerated
certificate's accepted `(program_digest, root, pred, count)` with the **original signed receipt**,
including the checker identifier. A signature and an unrelated valid certificate do not suffice:
`verify_receipt.py` requires every field to agree. The script also requires the three forged
certificates to be refused as well-formed inputs, and the deliberately weaker checker to accept
`open-lower`.

Verification never generates keys, replaces `allowed_signers`, signs new receipts, or overwrites
checked artifacts. The checked-in signer is a demo key, not an identity claim about a person or
organization. Its signature does not attest the checker binary or the source data.

Files: `program.json` (rules, strata, policy), `synth_transcript.py`, `project_transcript.py`, `extract_edb.py`,
`prove.py`, `forge.py`, `run.sh`, `allowed_signers`. Under `data/synthetic/{violating,fixed}/`:
`transcript.json`, `edb.json`, `certificate.json` (the checker's input: statement and certificate),
`check.out`, `receipt.txt`, `receipt.txt.sig`.
