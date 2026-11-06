# Substrate decision for the parser/language layer

2026-11-06. Fable deputy, second day of the automata program. Hub:
`AUTOMATA-ARITHMETIZATION-PROGRAM.md`; ceiling: `SEMANTIC-CEILING.md`; leaf interface:
`zkml-research/docs/LEAF-PROVER-DECISION.md` §6 and §6.1. Tags: [READ] seen at the cited
file:line; [MEASURED] a run or a pinned `#guard`; [CLAIM] asserted elsewhere, unchecked;
[INFERRED] derived here. Counts over clocks.

Ember's posture for this quest: ambitious but evaluable; every shape may change; decide the
substrate before grinding on legacy; nanodregg is not read, used or cited.

---

## 0. The decision, in five lines

1. **The substrate is the L2 rung in Lean**: a statement `(x ∋ c)`, an executable checker, the
   soundness theorem with the "relation or named collision" conclusion, the vacuity falsifier, and
   pinned counts. Everything new in this program lands there first and is complete there.
2. **AIRs are compilation targets, not the substrate.** Two targets exist: the BabyBear/Poseidon2
   v2 descriptor (`EffectVmDescriptor2`, served by `circuit` today) and the Tower256/cSHAKE trace
   (the leaf prover; its AIR layer does not exist yet, LEAF-PROVER-DECISION §6 "not yet
   available"). No new BabyBear AIR is written for a new family; new families get a Tower256 AIR
   when step (b) lands. Existing Lean-emitted BabyBear AIRs stay as the served carrier.
3. **Strangers run extracted checkers.** Each family's Lean checker is compiled to a native
   executable (`lake exe`), reads a JSON certificate, and prints the verdict with the statement it
   verified; that is the demo path, the microsite path, and the CI path. A STARK is shown where a
   descriptor is served today, on one record, with its verify time beside the native number.
4. **Rust crates**: `dfa` stays as the runtime dispatcher (ten dependents) but its compiler is
   conformance-tested against the Lean derivative decider and its `air.rs` is retired with the v1
   AIR; `audit`'s `CountProof`/`RangeProof`/`BudgetProof` are legacy statements, restated over
   `FixpointCert.verify`; `dregg-query` stays as the EDB source and MMR mirror, and its engine is
   superseded by the Lean checker for anything with rules; `zkoracle-prove/live` and `tokenizer`
   are out of this program's scope except for the one hand-built descriptor in `zk_leg.rs`.
5. **Costs are reported in substrate-neutral units** (rows, columns, lookups per symbol, degree)
   with the commitment term in two columns: Poseidon2 permutations (BabyBear) and Keccak-f
   evaluations (Tower256). The hub's "44 committed cells per byte" is a BabyBear number from today.

---

## 1. The facts that force it

| fact | tag | where |
|---|---|---|
| Leaves move to Tower256 with cSHAKE256 roots; "no algebraic hash (Poseidon2) for roots" | [READ] | minidregg `board/RULINGS.md` "Hashes" |
| The leaf's content binding is a cSHAKE Merkle root over the record's bytes, tied in-circuit by Keccak-f: 31 Keccak-f per 4 KiB record in char 2 | [READ] | LEAF-PROVER-DECISION §6 "Arithmetization the leaf should target" |
| No Lean AIR/zerocheck layer for Tower256 traces exists; "do not mirror; wait or ask" | [READ] | same, "Not yet available" |
| The served automata descriptors on BabyBear are `dregg-dfa-routing-table::exact-public-v1` and `dregg-dyck-parse-v1`; the toggle DFA `dfa-routing-toggle-2state::poseidon2-v1` is the predicate dispatch | [READ] | `circuit/src/descriptor_by_name.rs:83,104,172,403` |
| Weld8 is routed but refused by v2 assembly as non-graduated (`hash_sites`/`ranges` carriers non-empty) | [READ] | `circuit/src/descriptor_ir2.rs:2315-2320` |
| The Mac's `metatheory/.lake` is warm: Mathlib at `1c2b90b1` with oleans, 251 Dregg2 modules compiled; `lake env lean Dregg2/Datalog/FixpointCert.lean` passes in 17 s wall | [MEASURED] | this session, 2026-11-06 |
| hbox has no warm breadstuffs `.lake` (the predecessor's `~/lanes/fable-tower/bs`: packages fetched, zero oleans; `~/dev/bs-*`: none); root disk 42 GB free, 34 GB RAM free, ARC 28 GB | [MEASURED] | `ssh hbox`, this session |
| `dfa` is the runtime dispatcher for `cell`, `directory`, `wire`, `intent`, `teasting`, `wasm`, `dfa-federation`, `discord-bot`, `headver` | [READ] | `grep -l dregg-dfa */Cargo.toml` |
| `dfa/src/air.rs` is the trace shape of the v1 AIR (`circuit/src/dsl/dfa_routing.rs`; the test file its header names no longer exists), not an AIR; `dfa::compiler::Re::compile` is unproved against `determinizer_faithful` | [READ] | `dfa/src/air.rs:1-10`; hub §2 row "derivatives" |
| `audit::CountProof` never ties `global_index` to the inclusion path, `log_size` is unbound, `count = 0` verifies for any token and root; `RangeProof` never ties the timestamp to the leaf | [READ] | hub §2 rows "weighted", "timed" (lane B of 11-05) |
| The air-census: 111 Rust-built `EffectVmDescriptor2 {` literals in 51 files, among them `zkoracle-prove/src/zk_leg.rs:1` | [MEASURED] | `degg-research/experiments/air-census/RESULTS-2026-11-05.txt` |
| `FixpointCert` is L2 with 28 kernel-clean keystones and a closure leg; stratified negation, aggregates, the safe-program coincidence are named follow-ups | [READ] | `Dregg2/Datalog/FixpointCert.lean` header |
| Astra's 28-obligation audit of CERTIFICATES.md: 7 contract defects, 6 qualifications; CS12 (`cert_and` hypotheses), CS15 (bridge binding legs), CS18 (content-bound DFA's elided hypotheses) touch this program directly | [READ] | `zkml-research/notes/astra/certificate-statement-audit.md` |

---

## 2. Why L2 is the substrate (and what that rules out)

A proof system proves "the checker accepted". If the checker is a Lean function with
`verify_sound : verify x w = true → R x w ∨ Collision`, then every target that faithfully
arithmetizes `verify` inherits the theorem with one extra `ε_proof` term, and the *statement*
never changes when the target does. That is the only layer that survives the BabyBear → Tower256
move, so it is the one we invest in. Concretely, for every family:

- the Lean checker is total and executable (`decide`-free in its hot path, `#guard`-pinned);
- the soundness theorem's conclusion names the committed content and the word/EDB, or an explicit
  collision at a named pair (LEAF-PROVER-DECISION §6 shape; Astra CS18 says the bound DFA form
  must also carry "word-linked extracted trace, content-aware verifier"; we keep the extractor
  explicit and the verifier total over the word);
- the falsifier is a weaker checker's *acceptance* exhibited beside the strong checker's refusal
  (codex round 2 §1d made this the house rule);
- counts are stated per symbol / per firing / per candidate, with the commitment term separate;
- the checker is extractable: a `lake exe` target reads JSON and prints the verdict.

What this rules out: hand-written Rust AIRs (minidregg law C9, air-census W8); new BabyBear
descriptors for new families (they would be rewritten on Tower256 within weeks); "demo" numbers
that are STARK prove times over a BabyBear path the leaf will not use.

---

## 3. Crate-by-crate verdict

| crate / file | role today | verdict | action in this program |
|---|---|---|---|
| `dfa` (`compiler`, `router`, `filter`) | runtime DFA dispatch, 10 dependents | **keep as runtime** | conformance suite: the Rust `Pattern → Dfa` compile is checked against the Lean `Deriv` table (`tableDfa_faithful`) on a corpus of patterns; divergence is a red. A Lean-extracted `policyc` compiles the policy language to the same table encoding so the runtime can load Lean-compiled tables. |
| `dfa/src/air.rs` + `circuit/src/dsl/dfa_routing.rs` | v1 AIR trace shape | **legacy** | not extended; the v2 route is `DfaRoutingTableEmit.lean`. Retire when the v1 epoch ends. |
| `zkoracle-prove` / `zkoracle-live` | TLSNotary attestation + one BabyBear zk leg | out of scope | `zk_leg.rs`'s hand-built descriptor is a C9 hit; it is listed for the Lean-first generator, not touched here. |
| `tokenizer` | credential sealing (X25519 + ChaCha20) | out of scope | misnamed, not a tokenizer; the detokenizer family (hub `06`) has no consumer yet. |
| `turn-prover` | proof production for turns | out of scope | nothing automata-shaped. |
| `audit` (`CountProof`, `RangeProof`, `BudgetProof`) | token audit trail | **legacy statements** | restated over `FixpointCert.verify` (Count) and the weighted accumulator (Budget); the timed window waits on a timestamp-to-leaf binding. The old proofs stay until the restatement is served. |
| `dregg-query` | conjunctive queries + MMR mirror + CALM grade | **keep as EDB source and MMR mirror** | its "no IDB rules, no recursion, no stratification" line moves to the Lean checker: rules, recursion and strata are `FixpointCert`/`StratifiedCert`. `fact.rs`'s schema is the EDB flattening for demo (b). |
| `Circuit/Emit/{DfaRoutingTableEmit, DyckStackEmit, AttestedAutomatonWeld8, DerivationEmit, TinyAutomata*}.lean` | Lean-emitted BabyBear AIRs | **served carrier, frozen shape** | Weld8 is graduated (range-table lookups, limb split for `CURRENT < 2^15`) so the attested shape is served; no other new BabyBear AIR. Their counts remain the BabyBear column of every table. |
| `Crypto/Deriv/*`, `Crypto/Dfa.lean`, `Cfg*.lean`, `Datalog/FixpointCert.lean` | semantics + L2 | **the substrate** | extended additively (new files; shared declarations unmoved until the named flag day). |

---

## 4. Cost units from here

Per family, per record size `n ∈ {256, 4096, 65536}` bytes, a row of:

`rows · columns · lookups/symbol · degree | commit(BabyBear): ⌈n/8⌉+2 Poseidon2 perms · 352 cells | commit(Tower256): ⌈n/136⌉ Keccak-f (rate 1088 bits) + Merkle (cSHAKE per node)`

The Tower256 commitment column is [INFERRED] from LEAF-PROVER-DECISION §6's "31 Keccak-f per
4 KiB" (4096/136 = 30.1, plus the squeeze); it is a model number until the leaf AIR exists and
is marked so in `COUNTS.md`. The run term is substrate-neutral for table-routed families (one
lookup per symbol) and is where the families differ; the commitment term is shared by every
statement over one `c` and is the same for every family. The predecessor's two hot spots stand:
the `⌈n/8⌉+2` permutations are the BabyBear commitment and do not transfer; the unary length
framing (one row per symbol of padding) is a run-term cost and does transfer, so it is the one to
remove (binary length lane, LEAF-PROVER-DECISION §7 proposes the codec).

---

## 5. Where the plan was wrong, said plainly

1. **"100k documents with a receipt and verify time" is not a STARK-per-record demo today.** The
   served BabyBear descriptor proves one record's run; 100k STARKs is neither honest to build nor
   what the leaf will do. The honest demo (a): the corpus is an MMR; the padded-complement DFA is
   compiled by the Lean decider from the policy source; the per-record runs and the exact
   `Count = 0` are checked by the extracted Lean checker (verify = re-execution, time shown);
   **one** record is additionally proved under `dregg-dfa-routing-table::exact-public-v1` with its
   verify time shown, as the served-path evidence. The receipt is signed over
   `(policy digest, automaton digest, corpus root, N, count)`. The page says which leg is which.
2. **The route-commitment column is a BabyBear shape.** "+1 arity-2 chip lookup per row" prices a
   Poseidon2 chain. On Tower256 the word is bound by opening the cSHAKE Merkle root per position
   (or by the byte column *being* the committed column). The L2 statement
   (`traceWord trace = w ∧ commit w = c`) is the same for both; the per-family work is to state it,
   not to add the column. The milestone in hub §5.1 is restated as: every replay family's
   `*_refines_classify` theorem carries the `c` conjunct and the splice falsifier at L2.
3. **Weld8 graduation is worth doing and is BabyBear-only.** The committed-automaton shape on
   Tower256 is 16 cSHAKE compressions per row (§6.1 amendment 1): the price of policy privacy. We
   graduate the weld because ember asked and because it is the only served committed-automaton
   evidence; we do not extend it.
4. **Whole-tree hbox builds are a one-time setup, not a gate.** No warm cache exists on hbox; a
   cold `lake build` of the default targets compiles Mathlib-dependent Dregg2 plus Metatheory,
   Polis, Market, Bfv and the guard libs. The gate that runs on both machines is
   the family-check script lane C writes under `metatheory/scripts/` (planned name `automata-check.sh`): `lake env lean` on the family files (import closure
   from the warm cache), the `#guard` summary, and axiom reports. After this program touches a
   shared Lean structure, one whole-tree build on hbox under `swarm-build` (fresh clone under
   `~/lanes/automata`, `lake exe cache get`, `SWARM_MEM_MAX=12G`, PID file), with the disk number
   reported before and after; today that would leave ~34 GB free, above the 30 GB floor but close
   enough that the root is told first.
5. **The policy language is the front, and it is a Lean object.** `Lucid`'s `policy.forbid(...)`
   and our receipts both need one surface for patterns (with `neg`/`inter`), grammars, Datalog
   rules with strata, and budgets. The parser lives in Lean with the round-trip theorem; the
   executable is extracted. A Rust parser would be a second, unproved grammar.

---

## 6. The build command that works on this Mac (measured)

```
cd /Users/ember/dev/breadstuffs/metatheory
lake env lean Dregg2/Datalog/FixpointCert.lean        # 17 s wall, prints the #guard summary
lake build Dregg2.Datalog.FixpointCert                 # import-closure build, writes the olean
```

`.lake` is per-machine and gitignored (`lakefile.toml` header). The Mac's is warm; do not run a
bare `lake build` here (it would rebuild the default targets). Lane C's family-check script
wraps the family list.

---

## 7. Order of work (four lanes at once, Opus; the veteran keeps its quest)

| lane | quest | lands |
|---|---|---|
| A | stratified negation (`Datalog/StratifiedCert.lean`, per-stratum closure, forged-absence falsifier), weighted accumulators over exact Count (`Datalog/Aggregates.lean`, `seq_acc_is_fold`, tampered-row falsifier), then demo (b): the governance question over a `cv export --format json --redact` transcript, EDB flattening, extracted checker, signed receipt | Lean files, `lake exe datalog-check`, `demo/datalog-governance/` |
| B | the policy language: `Dregg2/Policy/{Syntax,Parser,Pretty,Elab}.lean`, round-trip theorem, located errors, elaboration to `Deriv.PredRE` / `Cfg` / `FixpointCert.Program` / budget claims, `lake exe policyc` | Lean files, the parser theorem, a `POLICY-LANGUAGE.md` note beside this one |
| C | build + counts + Weld8: the family-check script (Mac + hbox), the hbox one-time cache under `swarm-build`, `COUNTS.md` with the two commitment columns and the generating script, the Weld8 graduation so the weld is served, the C9 inventory for our families | scripts, `COUNTS.md`, Weld8 commits, `README.md` per family directory |
| D | demo (a): a public corpus slice of ≥100k documents, MMR root, padded-complement automaton from policy source, extracted checker, one served-descriptor STARK, signed receipt, microsite page in the house style | `demo/absence-receipt/`, `dregg-microsites/absence-receipt/` |
| E (after A or B frees) | LRAT checker in Lean (`Dregg2/Sat/Lrat.lean`, pigeonhole-3 `#guard`), derivative-bisimulation inclusion certificates (`Deriv/BisimCert.lean`, `noDoubleBraceRE ⊆ star any`) | Lean files, counts |

Cross-model: codex round 3 attacks this decision and lane A's statements before they land;
round 4 attacks the parser theorem and the LRAT checker. Both are appended to
`codex-synthesis.md`. Astra's audit is answered in `zkml-research/notes/astra/` after round 3.

---

## 8. Prior art for the substrate choice

[READ] Tantow et al. (ITP 2025) verify Datalog certificates in Lean with an extracted checker;
[READ] Coral (ZK CFG parsing) and Reef (2023/1886) both arithmetize a checker of a trace, not a
parser; [READ] ZKUNSAT (2022/206) arithmetizes a resolution checker; [CLAIM] minidregg law C9
("Lean-authored AIRs") is the house rule this generalizes. Not a first: "verify the certificate,
not the solver" is the standard pattern; ours is the pairing of that with the L0 content commitment
and the named-collision conclusion across every family.
