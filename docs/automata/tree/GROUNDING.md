# Tree automata over JSON/CBOR: grounding (initiative 12)

2026-11-06. Tree lane (Claude Opus 5.5), opened from `whatember/INITIATIVES.md` row 12. Hub:
`../AUTOMATA-ARITHMETIZATION-PROGRAM.md`; family note: `../07-tree-automata.md` (written 11-05,
nothing built). Tags: [READ] seen at the cited file; [MEASURED] a run or a pinned `#guard`;
[SEARCHED] a web result read this session; [INFERRED] derived here.

## 0. What I build, in six lines

1. `metatheory/Dregg2/Tree/`: a JSON value model (`JVal`), **deterministic CBOR** (RFC 8949
   §4.2.1) as its wire form with a proved decoder and `canon_injective`; a Merkleized tree root
   whose single paths open; a bottom-up deterministic tree automaton with run certificates; a
   compiler from the regular core of JSON Schema to that automaton with `compile_correct`.
2. Three content-bound statements, each data only and each concluding "the relation, or a
   collision at the pair the checker's extractor names" (the `Tower256ContentCert` shape):
   `schema_sound`, `path_pattern_sound`, `corpus_absence`.
3. The string leaf check is the house byte-table DFA (`Automata/TableRun.FlatTable`), so a leaf
   verdict is `Dfa.lean`'s `DfaAccepts` through `TableRunSpec.accepts_iff_dfaAccepts`, and a leaf
   digest is a `Dfa.ContentScheme` over the leaf's bytes (Layer B′ composition).
4. `corpus_absence` rides `Lightclient/MMR.lean` (`mroot_binds_or_collides`) over record roots,
   with the per-record evidence a **path opening** (only the opened path is disclosed).
5. `lake exe tree-check` (extracted Lean) is the verifier; a Rust crate produces certificates and
   calls the executable to verify (no Rust twin of the checker).
6. Demo: Claude Code tool-call records (`cv export --redact`), schema + "no `Bash` call's
   `input.command` contains `pkill -f`", Count = 0, microsite under `dregg-microsites/`.

## 1. What exists, and what I do with it

| object | where | status | here |
|---|---|---|---|
| tree-automata family note: `JTree`, `TreeAut` (hedge automaton, one horizontal DFA), `ser`, `toVpa`, route (i) vs route (ii) counts, label-blind falsifier | `docs/automata/07-tree-automata.md` | L0, nothing compiled [READ] | **reused** as the design of record; amended in §3 below |
| content-bound DFA (Layer B′): `ContentScheme`, `BoundStatement`, `dfa_bound_identifies_record_or_collides` | `Dregg2/Crypto/Dfa.lean:223-320` | L2 [READ] | **consumed** at the string leaf |
| flat byte-table DFA runner, `acceptsBytes`, spec `accepts_iff`, `accepts_iff_dfaAccepts`, `rejectCount_eq_zero_iff` | `Dregg2/Automata/TableRun.lean`, `TableRunSpec.lean` | L2, core-only executable [READ] | **reused** as the leaf automaton (same JSON table shape as `dfa-run`; `policyc compile --absence` produces it) |
| MMR: `mroot`, `mroot_binds_or_collides`, `server_cannot_omit_position`, `MRootColl` | `Dregg2/Lightclient/MMR.lean:493,780` | L2, abstract `hash : List ℤ → ℤ` [READ] | **reused** for the corpus; instantiated with SHAKE256 over a framed byte encoding (256-bit leaves), not the 1-felt BabyBear sponge the header prices at ~2^15.5 |
| executable SHAKE256 (KAT-pinned) | `Dregg2/Crypto/Keccak.lean:148` | [READ] | **reused** as the node hash (the deployed form is the leaf's cSHAKE256; the statement is abstract in the hash, as `DatalogCheck` already does) |
| `datalog-check`'s list encoding `enc : List ℤ → bytes` | `metatheory/DatalogCheck.lean:54-81` | injectivity checked by `#guard` only [READ] | **not reused**; my framing is proved injective (`frame_injective`), which is what lets a root collision be called a hash collision |
| `ContentCert` (statement of data; `Holds` decidable; `check_iff`; `named_or_collision` with the collision pinned at frames computed from the two trees) | minidregg `Compiler/Tower256ContentCert.lean` (on `lane/tower256-prover-exe`, `md-arklib` worktree) | L2 [READ] | **the interface I match**: same four-part shape; the tree root plays `contentRoot`, the schema digest plays `automatonRoot`, `ClaimData` gains `absent`/`count` |
| CFG certificates, `json_grammar()`, slot confinement | `Dregg2/Crypto/{Cfg,CfgCompact,SlotConfinement}.lean`, `zkoracle-prove/src/cfg.rs` | L1-L2 [READ headers] | **not on the tree path**: they certify JSON *text*. My statements are about the canonical tree; the text → tree projection is a named, re-runnable step (§4), not a theorem |
| Dyck/pushdown AIR | `Dregg2/Circuit/Emit/DyckStackEmit.lean`, `DyckStackReplay.lean` | served BabyBear, nesting ≤ 3 [READ COUNTS.md] | **not extended** (SUBSTRATE-DECISION §0.2: no new BabyBear AIR). Counts for route (i) cite its row shape |
| `FixpointCert` / stratified Datalog | `Dregg2/Datalog/` | L2 [READ] | **not used**: the regular core of JSON Schema is a bottom-up automaton, not Datalog; `uniqueItems`/`dependentSchemas` would be where Datalog enters, and they are out of scope (§3.2) |
| counts model | zkml-research `notes/construction-search/space.py --certs` → `docs/automata/COUNTS.md` | generated [READ] | **extended** with a `tree-*` family block (per node: transition lookups, child-wiring lookups, Keccak-f per node frame), not forked |
| demo (b) transcript projection | `demo/datalog-governance/transcript.json` | tool, path, spawned only [READ] | **not sufficient** (no command field). I project the same session's tool calls from `cv export --redact`, keeping `{name, input}` per call |
| tree automata in Lean anywhere in the tree | grep `TreeAut\|tree automat` over `Dregg2` | 0 hits outside the note [READ census, rechecked] | built here |

## 2. Prior art: what each proves, what this adds

| work | proves / provides | relation to this |
|---|---|---|
| Coral, ePrint 2025/1420 (S&P 2026) [READ in note 07] | ZK proof that committed bytes parse under a CFG into an LCRS tree in segmented memory, then field facts (JSON, TOML) | closest. It certifies parse + selection; no tree automaton over the result, no absence over a committed corpus, no canonicalization theorem (JSON text is the content, so two spellings of one value are two contents) |
| Pluto `web-prover-circuits` [SEARCHED] | Circom JSON parser + key-path extractor over decrypted TLS bytes | value extraction at one path; a hand-written circuit, no machine-checked statement; escapes are matched at the byte level |
| zkJSON (WeaveDB) [SEARCHED] | an encoding of JSON into field elements and Circom proofs of a value at a path | selective disclosure; no schema, no absence, no canonicality argument |
| EverCBOR / EverCDDL (Ramananandro et al., arXiv 2505.17335) [SEARCHED] | verified C/Rust parser+serializer for deterministic CBOR, **non-malleability of the deterministic fragment**, floats excluded | the wire-form theorem I mirror in Lean on a smaller model (`decode_encode`, `canon_injective`); they validate CDDL, not tree automata, and have no commitments |
| Bruyère, Pérez, Staquet, TACAS 2023 [READ note 07] | JSON Schema ≡ VPA under a fixed key order; streaming validation | I fix key order by canonicalization (CBOR §4.2.1 order), which is what turns `required` over `k` keys into `O(k)` horizontal states instead of `2^k` |
| Attouche et al., POPL 2024; Pezoa et al., WWW 2016 [SEARCHED] | formal semantics of JSON Schema; Draft-04+ exceeds tree automata; validation PTIME-complete | fixes the scope: I compile the regular core only and say which keywords are refused |
| RFC 8785 (JCS) | canonical JSON via ES6 number serialization and UTF-16 key order | **rejected** as the canonical form, see §3.1 |
| Lean `Lean.Json` | an unverified parser (numbers as `JsonNumber`, objects as RB-maps, duplicate keys last-wins) | not used as the model: last-wins silently resolves the duplicate-key ambiguity an attacker wants |

What this adds, as far as the searches reached ("no hit" is not "none exists"): a machine-checked
statement that ties a tree automaton's verdict to a Merkle commitment of a canonical tree, a
single-path opening composed with a content-bound byte DFA, and absence over an MMR-committed
corpus whose per-record evidence discloses only the opened path.

## 3. Where the bar moves (peer's amendments)

1. **Canonical form: deterministic CBOR with exact decimals, not JCS.** JCS canonicalizes the
   I-JSON model (IEEE doubles), so it is injective there but *not* on JSON values as written:
   `9007199254740993` and `9007199254740992` serialize identically, and `1e400` has no double at
   all. The model's numbers are exact decimals `m·10^e` normalized
   (`m` not divisible by 10, zero is `0·10^0`); integers encode as CBOR major types 0/1 in shortest
   form, non-integers as tag 4 (decimal fraction, RFC 8949 §3.4.4). `-0` and `0` are one value.
   Admitted domain: integer magnitudes and mantissas below `2^64`, exponents in `[-2^63, 2^63)`;
   outside it the projection refuses the record (counted, never silently rounded).
2. **Unicode is not normalized.** NFC `é` and NFD `e◌́` are two trees (JCS and CBOR agree). A
   byte pattern over the decoded leaf is evaded by a homoglyph; that is the pattern's meaning, not a
   soundness gap, and the demo says so. Escapes **are** decoded: `"pkill -f"` is the leaf
   `pkill -f`. A flat byte scan of the raw JSON misses it and the tree certificate does not; that
   pair is the flagship falsifier for "flat-string claim vs tree certificate". Lone surrogates are
   refused (CBOR text must be UTF-8).
3. **Duplicate keys are refused**, at projection and in the decoder (map keys strictly increasing
   in encoded-byte order). `serde_json::Value` and Python keep the last duplicate, so
   `{"command":"ls","command":"pkill -f x"}` reads differently under two parsers; a canonical tree
   cannot express it.
4. **Two commitments in one statement.** Route (ii) (Merkle AST) is what single-path opening
   needs; route (i) (bytes) is cheaper for whole-tree checks (note 07 §3). The statement carries the
   tree root; `canon_injective` makes the CBOR bytes a function of the tree and vice versa, so a
   byte commitment of the canonical encoding and the tree root name the same record (this is the
   L5 morphism note 07 §4 said JSON cannot have; canonical CBOR has it).
5. **Absence is selective, not re-execution.** The per-record evidence for "no record has a
   match" is a path opening (sibling keys and digests only), or a refutation at a different
   conjunct (the record's `name` is not `Bash`). A re-run over whole records would disclose every
   file the agent read.
6. **The corpus hash is 256-bit.** `MMR.lean`'s own header prices its 1-felt sponge at ~2^15.5
   queries; I instantiate `mroot` with SHAKE256 over a proved-injective framing.

### 3.2 Schema scope (regular core)

Compiled: `type`, `const`/`enum` (strings, finite), string `pattern` as a byte DFA, integer and
decimal bounds, `properties`/`required`/`additionalProperties` (false or a schema), `items` (one
schema for all), `minItems`/`maxItems` (bounded counter states), `anyOf`/`allOf` over the same
node (acyclic), `$ref` recursion across levels. Refused with a named error: `uniqueItems`,
`dependentSchemas`, `unevaluatedProperties`, `patternProperties`, `oneOf`, `multipleOf`.

## 4. Trust boundary, stated once

The certificate's statement is about the canonical tree (equivalently its CBOR bytes). The step
JSON text → tree (escapes decoded, numbers normalized, keys sorted, duplicates refused) is a
projection, computed by the Lean parser inside `tree-check` and reproducible by a stranger from the
`cv export --redact` output; it is not proved against RFC 8259's grammar (the CFG family certifies
text, and the route (i) weld is where the two would meet). The Rust producer is untrusted: the Lean
executable re-decodes its CBOR, re-checks canonicality (`encode (decode b) = b`), and recomputes
every root.

## 5. Plan and gates

| step | lands | gate |
|---|---|---|
| L1 | `Tree/{Value,Cbor,Merkle,Automaton,Schema,Cert}.lean`, statements + falsifiers as `#guard`s | statement audit (codex, adversarial on `canon_injective`, `corpus_absence`) |
| L2 | proofs; `lake exe tree-check`; `automata-check.sh` family list; counts block in `space.py` | `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; automata-check green |
| L3 | Rust producer (`tree-cert` crate), demo corpus, receipt, microsite, re-verify command | a stranger's re-run from the committed inputs; second codex round |

## 6. Decisions only ember can make

- **Publishing the demo corpus.** `{name, input}` of every tool call of session `e3ba49ed`
  (redacted by `cv export --redact`) is more than demo (b)'s path-only projection; whether either
  goes to public GitHub is already open as INITIATIVES decision (1). Until you say, the corpus
  file is kept out of git and only its MMR root, record count and one opened path go in.
- Whether the `Tree/` statements should move to minidregg's Tower256 leaf when its AIR layer
  lands (the shape matches; the hash changes from SHAKE256 to its cSHAKE256 cube-Merkle).
