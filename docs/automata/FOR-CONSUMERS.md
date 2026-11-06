# For the lanes that build on these families (streaming certificates, tree automata, and later ones)

2026-11-06, the parser/language deputy. Initiatives 11 (streaming certificates: prefix receipts over
a live log, Büchi/ω) and 12 (tree automata over JSON/CBOR transcripts) coordinate through this
directory; put your `GROUNDING.md` here and ask questions in it, I answer in `codex-synthesis.md`
or beside your file. Tags as everywhere: [READ]/[MEASURED]/[INFERRED]/[CLAIM].

## What exists that you should reuse, not rebuild

| object | where | what it gives you |
|---|---|---|
| the substrate rule | `SUBSTRATE-DECISION.md` §2 | a family is done at L2: statement with the content root, executable checker, `verify_sound` with "relation ∨ named collision", the weaker checker's ACCEPTANCE beside the strong one's refusal as named theorems, pinned counts, extracted executable; six per-target obligations before any AIR |
| content binding | `Dregg2/Lightclient/MMR.lean` (`mroot`, `MRootColl`, `mroot_binds_or_collides`, `server_cannot_omit_position`); `Dregg2/Datalog/FixpointCert.lean` (`flatten`, `flatten_injective`) | commit a list of integers; non-omission over a committed log is exactly what a prefix receipt needs (note `10-omega.md` §binding) |
| stratified Datalog with exact Count | `Dregg2/Datalog/{StratifiedCert,JoinClosure,SafeCoincidence,Aggregates}.lean`; `lake exe datalog-check` (`metatheory/DatalogCheck.lean`) | `verifyS_receipt` (root, exactness, count, supported model in one statement); `verifyJ_sound_unrestricted` (what the executable accepts is the standard stratified model); budgets over exact Count. The executable reads `{"statement", "certificate"}` JSON; `policyc rules` emits the program in that shape |
| the policy language | `Dregg2/Policy/*`, `lake exe policyc`, `POLICY-LANGUAGE.md` | `parse_print_roundtrip (hwf : p.wf = true)`, `elabRe_semantics`, `absenceOf_semantics`; `policyc compile --absence` emits a table with its own correctness proof (`Factor.absence_decides`); long counted repeats are slow (cubic in the count) |
| DFA runs and their binding | `Dregg2/Crypto/Dfa.lean` (`BoundStatement`, `dfa_bound_identifies_record_or_collides`), `Dregg2/Automata/{TableRun,TableRunSpec}.lean` + `lake exe dfa-run`, `Dregg2/Circuit/Emit/*Bound.lean` | the content-bound shape every word-level claim must take; which served families bind the word today (only the hash-chained routing; table routing exposes a transition multiset; the weld binds the automaton, not the word) |
| SMT-shaped certificates | `Dregg2/Sat/LratCert.lean`, `Dregg2/Crypto/Deriv/BisimCert.lean` | UNSAT by LRAT; policy inclusion/equivalence by derivative bisimulation, both policies committed by `mroot` |
| counts and the gate | `COUNTS.md` (generated, pins re-read), `metatheory/scripts/automata-check.sh`, `BUILD.md` | add your files to the gate list; cite `#guard` pins by file:line; run the gate before every commit (under two minutes on the Mac, 18 s on hbox) |
| demos | `demo/datalog-governance/`, `demo/absence-receipt/` | the receipt shape `(digests…, root, N, count)` signed with `ssh-keygen -Y`; what each README refuses to claim is the template for yours |

## Rules you inherit

- Public data only in anything committed; nothing session-derived (ember's rule of 2026-11-06, pending the
  `transcript.json` decision). A demo over "real transcripts" means a SYNTHETIC or public transcript
  unless ember says otherwise; lane A's `synth_transcript.py` (in flight) is the pattern.
- Every negative or universal claim ("no window violates", "the tree has no node of kind K") is a
  closure or an enumeration; price it as such (SEMANTIC-CEILING.md §0 and §1.2).
- The encoding is part of the statement: injectivity of your byte/felt codec, range checks, and the
  framed length are obligations, not residuals (codex round 3 finding 2); `flatten_injective` is over
  `List ℤ` only.
- Streaming (11): the prefix semantics is `GoodPrefix`/`BadPrefix` of an ω-language (note `10`); a
  per-window receipt is the DFA/Datalog certificate over the window plus the MMR opening of the
  window's range against the current root, and "so far" is the monotone (CALM) side: positive rules
  extend, negation and Count re-run closure at the new root (note `13` §6).
- Tree automata (12): the VPA route reuses the Dyck/bracket machinery (`04-vpa-dyck.md`, note `07`);
  the streaming form of a schema is a VPA over the serialization; modern JSON Schema exceeds tree
  automata, so state which regular core you claim. Dyck's route is being made a function of the word
  (two gates approved 2026-11-06); until that lands, state two-trace theorems as `DyckStackBound.lean` does.
- Codex (`codex exec -c model="gpt-6-astra" --sandbox read-only`) attacks your statements before they
  land; append the round to `codex-synthesis.md` with verdicts.
