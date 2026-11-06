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

**What L2 does not do (codex round 3, findings 1-2, adopted).** The semantic theorem is reusable;
the cryptographic implementation is not. Each target must separately establish, and the counts
table must name as rows: (i) canonical public-input decoding; (ii) accepted-trace refinement to
`verify` (the arithmetized checker is the Lean checker); (iii) checker/program identity (the
extracted executable or the AIR is the function the theorem is about); (iv) existential
soundness or, where the conclusion is a named collision, the efficient extractor the reduction
needs; (v) an error bound stated in the ADAPTIVE transcript experiment (a randomized check
`e₀ + α·e₁ = 0` accepts `(α, −1)` chosen after `α`); (vi) an injective, framed codec on the
admitted domain with range checks on every encoded value, bounded-limb integer arithmetic, and
the exact length and positions the checker consumed. Encoding aliases (`e(0)` vs `e(p)` under a
modular hash, `1 + 1 = 0` in a characteristic-2 accumulator, `[a]` vs `[a, 0]` under zero
padding) are implementation failures, never hash-collision residuals; `flatten_injective` is
injectivity over `List ℤ`, not over bytes.

What this rules out: hand-written Rust AIRs (minidregg law C9, air-census W8); new BabyBear
descriptors for new families (they would be rewritten on Tower256 within weeks); "demo" numbers
that are STARK prove times over a BabyBear path the leaf will not use.

---

## 3. Crate-by-crate verdict

| crate / file | role today | verdict | action in this program |
|---|---|---|---|
| `dfa` (`compiler`, `router`, `filter`) | runtime DFA dispatch, 10 dependents | **keep as runtime** | conformance suite: the Rust `Pattern → Dfa` compile is checked against the Lean `Deriv` table on a corpus of patterns; divergence is a red. This is REGRESSION evidence only: it does not discharge `tableDfa_faithful`'s agreement premise, and the runtime routes by longest-prefix acceptance while a content certificate binds the whole word (codex round 3, finding 6). Certified policies use Lean-produced tables. |
| `dfa/src/air.rs` + `circuit/src/dsl/dfa_routing.rs` | v1 AIR trace shape AND a live native witness API (`verify_acceptance`, called by `cell/src/predicate.rs` `DfaAcceptanceVerifier` and `cell/src/interface.rs` route membership) | **the descriptor is legacy; the native API is live and was unsound** | codex round 3 finding 3 [READ, confirmed at `dfa/src/air.rs:235`]: the table, start and accepting set were read off the proof and never authenticated against `router_root`; an empty trace with the copied root verified for any input, and a trace over a shorter accepting prefix re-classified the input. Fixed 2026-11-06 (the verifier recomputes the commitment from the proof's table, derives acceptance from the committed accept-map, and requires the longest-match span; five forgery tests pinned red). The `RouteTableBuilder` commitment also never covered `prefix_lens` despite its docstring; fixed in the same commit. The v1 descriptor stays unextended. |
| `zkoracle-prove` / `zkoracle-live` | TLSNotary attestation + one BabyBear zk leg | out of scope | `zk_leg.rs`'s hand-built descriptor is a C9 hit; it is listed for the Lean-first generator, not touched here. |
| `tokenizer` | credential sealing (X25519 + ChaCha20) | out of scope | misnamed, not a tokenizer; the detokenizer family (hub `06`) has no consumer yet. |
| `turn-prover` | proof production for turns | out of scope | nothing automata-shaped. |
| `audit` (`CountProof`, `RangeProof`, `BudgetProof`) | token audit trail | **unsound verifiers of still-needed statements** | the statements (exact usage count, a timestamp in a window, remaining budget) are needed; the verifiers are not evidence of them (`count = 0` verifies for any token and root). Restated over `FixpointCert.verify` and the weighted accumulator, PRESERVING event-occurrence semantics: facts carry an authenticated occurrence id (position), token identity, snapshot coverage; `addFact` deduplicates, so two identical events at two positions must be two facts (codex round 3, finding 5). The old formats may stay readable; their verification is not trusted. |
| `dregg-query` | conjunctive queries + MMR mirror + CALM grade | **keep as EDB source and MMR mirror, with one named obligation** | its "no IDB rules, no recursion, no stratification" line moves to the Lean checker: rules, recursion and strata are `FixpointCert`/`StratifiedCert`. Obligation (codex round 3, finding 4 [READ `dregg-query/src/attested.rs:149,269`, `receipt.rs:120`]): the MMR opening authenticates receipt hashes and positions, not the `effects` array that fact extraction reads; dropping a `Revoked` effect leaves the opening valid and the EDB wrong. The EDB must be proved to be the complete deterministic extraction of AUTHENTICATED receipt contents at the named snapshot (effect disclosures and heights bound, positional coverage preserved, the Rust-to-Lean fact codec faithful) before a `FixpointCert` over it says anything about the log. Demo (b) uses `cv` transcripts, not receipts, and states this. |
| `Circuit/Emit/{DfaRoutingTableEmit, DyckStackEmit, AttestedAutomatonWeld8, DerivationEmit, TinyAutomata*}.lean` | Lean-emitted BabyBear AIRs | **served carrier, frozen shape** | Weld8 is graduated (range-table lookups, limb split for `CURRENT < 2^15`) so the attested shape is served; no other new BabyBear AIR. Their counts remain the BabyBear column of every table. |
| `Crypto/Deriv/*`, `Crypto/Dfa.lean`, `Cfg*.lean`, `Datalog/FixpointCert.lean` | semantics + L2 | **the substrate** | extended additively (new files; shared declarations unmoved until the named flag day). |

---

## 4. Cost units from here

Per family, per record size `n ∈ {256, 4096, 65536}` bytes, a row of:

`rows · columns · lookups/symbol · degree | universal leg (closure candidates, rejection checks) | commit(BabyBear): ⌈n/8⌉+2 Poseidon2 perms · 352 cells | commit(Tower256): ⌊n/136⌋+1 Keccak-f for the payload sponge (FIPS 202 Alg. 8: padding included, no extra squeeze for one 32-byte output; so 136 bytes is 2, 4096 is 31, empty is 1) + the cSHAKE customization prefix of SP 800-185 §3.3 unless precomputed + the Merkle nodes + the length framing`

The Tower256 payload-sponge column matches LEAF-PROVER-DECISION §6's "31 Keccak-f per 4 KiB"
(codex round 3, finding 15, corrected the derivation: `⌊n/136⌋+1`, not `⌈n/136⌉` plus a
squeeze); it is a payload estimate, not the full commitment price, until the leaf's framing and
Merkle topology are fixed, and `COUNTS.md` says so. A "lookup" is an abstract operation whose
rows/columns/degree are target-dependent: the table reports the operation count and, per
target, its deployed realization with a file:line (finding 16). The run term is substrate-neutral for table-routed families (one
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

---

## 9. Ceremonies on the Lean → descriptor → Rust path: what each protects, and a verdict

Ember, 2026-11-06: "we maybe need to reevaluate how necessary some of these ceremonies are."
One page. The path: a Lean emitter (`#guard`-pinned) → `scripts/emit_descriptors.py` →
`circuit/descriptors/**/*.json` + `*_FP` sha256 constants in Rust → `include_str!` in the prover
→ the recursive VK hash. Each row names the concrete failure the ceremony would catch, the
evidence of whether it does, and keep / simplify / delete. "Script" below means: runs in under
five minutes on a lane's machine, no environment variable, no human in the loop, red is a line
in the commit it refuses.

Evidence first [MEASURED, this session]: `circuit/descriptors/PROVENANCE.json` was last stamped
2026-08-11; `docs/VK-REGEN-LOG.md` has no emit row since; `attested-automaton-map-committed-weld8-v1.json`
(the predecessor's, `9208cc055`) and `dregg-cert-qp-portfolio6-s3-ir2.json` are checked in with no
stamp row, so the standing `provenance --rev HEAD` gate is red at HEAD and has been for weeks with
nothing refusing; the drift gate is a 330-minute CI job skipped on push (nightly only); `ci.yml` has
zero successes in its last 40 runs; `local-gates.sh` has 147 rows and is run by hand; the pre-push
hook blocks on two of them. The federation the re-key ceremony protects is `deploy/aws/SUPERSEDED`.

| # | ceremony | protects against (concrete failure it catches) | evidence it does | verdict |
|---|---|---|---|---|
| 1 | Lean `#guard` pins and `#assert_all_clean` in every emitter; the five `emitVmJson2 … == "…"` string pins | a Lean edit that silently changes columns, constraints, PIs or axioms of a served object | runs at every `lake env lean`; it is what "Lean owns acceptance" means | **keep** (it is a build, not a ritual) |
| 2 | `emit_descriptors.py` default mode: emit, route, install, **re-pin `*_FP` sha256 constants into Rust source** | a hand-edited JSON | the FP is sha256 of the file beside it: self-consistency, and `check-descriptor-drift.sh:6-10` says so itself; `provenance_json_pins_match_…` is the same tautology one altitude up | **simplify**: keep emit+route as the one script; **delete the `*_FP` re-pin** and the derived-coverage test; a descriptor's identity is its canonical-bytes fingerprint computed at load (`DescriptorCanonical`, Lean and Rust, with the standing differential) |
| 3 | `check-descriptor-drift.sh --rev HEAD` (re-derive every descriptor from Lean, diff) | a Lean change committed without re-emitting; real: three lanes' stale fixtures on 2026-07-31 | the right check at the wrong cadence: 330 min, nightly, in a CI nobody receives | **keep as a script, change the trigger**: re-derive only emitters whose import closure moved since the last emit (`--list-emitter-modules` already computes the closure), run on hbox nightly under `swarm-build`, verdict written to a board file and to the next commit that touches `circuit/descriptors/` |
| 4 | **`PROVENANCE.json` ack-gated stamp**: `DREGG_VK_REGEN_ACK=<tree hash>`, `ALLOW_DIRTY`, the detached-worktree emit protocol, `--verify-provenance`, `--strict` | a regen from an unreviewed or dirty Dregg2 tree re-keying a live federation; a descriptor byte differing from its stamped sha | not taken in three months; two served descriptors unstamped at HEAD; its own doc records "months at zero invocations" and three lanes stuck in the ALLOW_DIRTY loop; the federation is superseded | **delete** the ack, the stamp and `--strict`. "Which Lean tree minted these bytes" is the emit commit (git); "are the bytes what Lean says" is row 3; "is this the deployed program" is the deploy side's pinned fingerprint set (row 8's closure test). Keep **`--verify-by-name-routing`** (static `EmitByName.lean` ↔ `by-name/` ↔ disk reconciliation, seconds): make it a pre-commit check when either is staged |
| 5 | `docs/VK-REGEN-LOG.md` (append-only regen log) + `check-schema-epoch-log.py` (event row per `CANONICAL_STATE_SCHEMA_EPOCH` bump) | reconstructing epoch history; a constant bumped with no record (real: `6441705e8`) | the log stopped at 2026-08-11; the epoch check is duplicated by the Rust test `dregg_persist::schema_epoch_log_row` | **simplify**: delete the markdown regen log (`git log -- circuit/descriptors` is the log); keep the epoch ledger as the Rust test only, delete the script twin |
| 6 | By-name golden re-emit: the hand-kept `EMITTERS` list in `emit_descriptors.py`; `check-emitter-routing.sh` | an emitter absent from the list never re-runs on a flag day, so its artifact goes stale (real: 07-31, three lanes) | the list is the defect; the check polices the list | **simplify**: derive the emitter set from the tree (`Emit*.lean` glob plus a one-line `-- emits:` header), so there is no list to forget and the check is the emit |
| 7 | Emit-gate weld: 22 `circuit-prove/tests/*_emit_gate.rs` tests carrying a `GOLDEN_JSON` literal, policed by `check-emit-gate-weld.py` against the Lean string pins | the Rust copy and the Lean copy of one JSON drifting while both stay green | a gate that compares two copies of one claim | **delete** the Rust golden copies: the Rust test `include_str!`s the emitted file (one copy), the Lean `#guard` pins the emission; the script goes with them |
| 8 | VK pin literals: fourteen typed-in `*_VK_LANES` nine-lane fingerprints; `vk_pin_closure_over_the_served_tree`, `descriptor_pin_literals_are_not_transcriptions`, `CheckVkPinLiterals.lean`, the canonical-encoder differential | a pin naming a program the tree does not have, or stale after a re-emit (real: ten in one week) | the closure test is a real test; the literals are the defect | **keep** the closure test and the Lean-vs-Rust encoder differential (a wrong encoder fails silently); **simplify the literals away**: `DescriptorCanonical.canonicalBytes` exists in Lean, so a `vk_pin` is computed from the pinned descriptor term at emit time and never typed |
| 9 | Descriptor-anchor inertness ratchet, chip-absorb-arity admission, PI-disposition census | a public input no gate mentions (real: Solana, eleven anchors); a chip arity the chip AIR cannot satisfy (real: arity 9 since day one) | semantic checks on the emitted object, done in Rust after the fact | **keep, move into Lean**: an emitter `#guard` that every PI column occurs in a gate or lookup tuple, and that every chip site's arity is admitted (the admitted set mirrored in Lean and covered by the differential); the Rust scripts remain as differentials, not gates |
| 10 | `local-gates.sh` (147 rows, by hand) and the 87-minute CI | everything above, in principle | zero green CI runs in 40; "invoked BY HAND" | not this program's to delete wholesale; for the automata families the gate is **one script** (row 1 on the family files, axiom reports, row 4's routing check), under five minutes, run before each commit and named in the commit message; rows 4, 5 and 7 leave the table |

Why the verdicts lean to delete: on the Tower256 leaf path there is no descriptor JSON at all.
Acceptance is the compiled Lean checker (`check_iff`), the receipt codec is Lean, and the
"VK" is the checker's own identity. Every ceremony in rows 2, 4, 5 and 7 exists to bridge a
Lean object to a Rust copy of it; where Lean owns acceptance the copy does not exist and the
ceremony has nothing to protect. What survives is exactly what still has two independent
witnesses to reconcile: Lean's emission against a checked-in cache (row 3), Lean's canonical
encoder against Rust's (row 8), and the static routing table against disk (row 4's keeper).

**Amended after codex round 3 (findings 7-14; adopted).** The attack on rows 3-4: emit from an
uncommitted weakened Lean source, restore it, commit only the descriptor; the emit commit does not
contain the generating source, and `source_dirty=true` was the only refusal. So the verdict is
"delete the human ceremony, keep the automatic record": the ack, `ALLOW_DIRTY`, `--strict` and
`--stamp-existing` go; the emit always runs from a committed revision in a detached worktree
(`--rev`, which exists) and writes the stamp (tree hash, toolchain, emitter list, per-file sha256)
with no human in the loop; `--verify-provenance --rev HEAD` stays as a script. Row 2: the `*_FP`
tripwire catches a descriptor-only edit that no source-closure trigger would select; it stays
until the re-derive triggers on artifact changes too. Row 5: the Rust epoch test checks only the
latest row and `include_str!`s the markdown log; the log file and the ledger script stay, only the
emit's regen-row writer goes. Row 7: the weld script also covers production inline descriptors and
JSON fragments (a `turn-prover` prefix kept width 3804 after emission moved to 3826); the test
goldens become `include_str!`, the script is narrowed, not deleted. Row 8: the closure test does not
establish the intended target, so row 4 may not cite it as "is this the deployed program". Row 9:
port the connectivity/ratchet semantics, not occurrence counting (an anchor in a unary range lookup
is still inert). Controls: a deleted leg's failure fixture must be REJECTED by the surviving check;
"red-then-gone" shows loss of detection, not preservation.

Who executes: lane C2, one commit per row with the fixture-against-survivor control recorded; the
emitter-set derivation (row 6) must reconcile declared outputs against served consumers and disk
in both directions and fail closed; the pin-literal removal (row 8) is a flag day on the Mina
modules and is proposed, not done, here.
