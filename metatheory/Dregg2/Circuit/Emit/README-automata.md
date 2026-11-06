# Automata emitters (`Circuit/Emit/`)

2026-11-06, lane C of the automata program. These are the Lean-emitted BabyBear AIRs for the automata
families, the "served carrier, frozen shape" of `docs/automata/SUBSTRATE-DECISION.md` §3: no new BabyBear
AIR is written for a new family; these stay as the served carrier and their counts are the BabyBear
column of `docs/automata/COUNTS.md`. Tags: [MEASURED] a `#guard` pin at the cited line; [READ] read off
the file.

## Gate

```
cd metatheory
scripts/automata-check.sh            # includes every emitter below that is on the program list
scripts/automata-check.sh --files Dregg2/Circuit/Emit/AttestedAutomatonWeld8.lean,Dregg2/Circuit/Emit/AttestedAutomatonLanes8.lean
```

`#guard` is compiled evaluation: green means every shape pin, golden string and falsifier verdict in
the file held. Each emitter's full Lean output is in the log directory the script prints.

## The objects

| emitter | object | served descriptor (`name`) | counts [MEASURED] | theorem |
|---|---|---|---|---|
| `DfaRoutingTableEmit.lean` | DFA run as one exact-public table lookup per row, `(state, sym, next)`; the run itself is the table | `dregg-dfa-routing-table::exact-public-v1` (`circuit/src/descriptor_by_name.rs:104`) | 3 columns, 2 PIs, 4 constraints, 1 table (`metatheory/Dregg2/Circuit/Emit/DfaRoutingTableEmit.lean:540`); wire string byte-pinned at `:536` | `tableRouting_refines_classify` (`:438`): a satisfying trace's final state is `classifyFrom` of its SYMBOL column; the word is not bound to a commitment |
| `DfaRoutingGeneralEmit.lean` | hash-chained routing for a 3-state injection DFA: interpolant transition gate, per-row entry hash, running hash seeded at the table commitment | `dfa-routing-injection-3state::poseidon2-v1` (emitted, not routed by name) | 22 columns, 4 PIs, 14 constraints, two chip lookups per row (`metatheory/Dregg2/Circuit/Emit/DfaRoutingGeneralEmit.lean:272`) | modelled by `DfaAcceptanceAir.dfaAir_verify_sound` and `route_commitment_binds_trace` (`metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:526`, `:418`) |
| `DfaRoutingEmit.lean` (sibling, not on the gate list) | the same chained shape for the 2-state toggle | `dfa-routing-toggle-2state::poseidon2-v1` (`circuit/src/descriptor_by_name.rs:83`) | see the file's own pins | `DfaRoutingRefine.lean`, `DfaRoutingRung2.lean` |
| `DyckStackEmit.lean` | leftmost-derivation replay of `S → [S] \| ε` as a fixed-depth (5) stack log, nesting capped at k ≤ 3 | `dregg-dyck-parse-v1` (`circuit/src/descriptor_by_name.rs:172`) | 24 columns (`:639`: `DYCK_WIDTH + 14 == 38`), 4 PIs, 79 constraints (`metatheory/Dregg2/Circuit/Emit/DyckStackEmit.lean:629`), two narrow chip lookups per row | the emit is the object; the theorem is in `DyckStackReplay.lean` |
| `DyckStackReplay.lean` | decodes a satisfying Dyck trace back into a compact rule sequence | (same descriptor) | 5 decoded rows and 2 rules for the word `[ ]` (`metatheory/Dregg2/Circuit/Emit/DyckStackReplay.lean:963`) | `parse_sat_imp_replay_emit_unconditional` (`:934`): satisfaction implies `ReplayAccepts dyck` of the decoded word; `PI_TABLE`/`PI_ROUTE` are absent from the statement (note `04-vpa-dyck.md`) |
| `AttestedAutomatonEmit.lean` (sibling) | committed-automaton replay with a scalar root: one map-op READ per row, key `2·current + symbol ↦ next` | `dregg-attested-automaton::map-committed-v1` (`:396`) | 4 columns, 3 PIs, 6 constraints, 1205 bytes (pinned beside the weld, `AttestedAutomatonWeld8.lean:950`) | `forged_edge_refused` (`metatheory/Dregg2/Circuit/Emit/AttestedAutomatonEmit.lean:1131`) |
| `AttestedAutomatonWeld8.lean` | the 8-felt-root weld of the attested shape, graduated 2026-11-06 (range-table lookups, empty `hashSites`/`ranges`) | `dregg-attested-automaton::map-committed-weld8-v1` (`circuit/src/descriptor_by_name.rs:180`) | 11 columns, 10 PIs, 22 constraints, 3 tables, 0 declared rows, 0 nonlinear multiplications (`metatheory/Dregg2/Circuit/Emit/AttestedAutomatonWeld8.lean:943`); 2803 wire bytes constant in word length and table size (`:957`); 16 chip permutations per row (`:980`) | `forged_edge_refused_8` (`:335`), `weldWit_satisfies` (`:837`) |
| `AttestedAutomatonLanes8.lean` | the weld's denotation through all eight root lanes | (same descriptor) | no shape pins of its own | `weld8_forged_edge_refused` (`metatheory/Dregg2/Circuit/Emit/AttestedAutomatonLanes8.lean:471`): a row whose NEXT disagrees with the committed automaton yields a map-root collision at a named pair |
| `TinyAutomataLanesK.lean` | k DFAs run side by side over one word: k state columns, k lookups per row | none (measured objects) | k = 1..4: widths 3/5/7/9, constraints 4/8/12/16, tables 1..4, trace pinned at 8 rows for the 8-symbol probe (`metatheory/Dregg2/Circuit/Emit/TinyAutomataLanesK.lean:784`); area against product-first 24 flat (`:796`) | `lanesKWit_satisfies` (`:456`): the witness exists at every k |
| `DerivationEmit.lean` | one Datalog rule firing: head = `hash_fact`, body facts opened against `state_root` | `dregg-derivation-v1` (`circuit/src/descriptor_by_name.rs:167`) | 386 columns, 393 constraints, 13 PIs (`metatheory/Dregg2/Circuit/Emit/DerivationEmit.lean:393`, `:397`, `:398`) | `derivation_sat_imp_authentic` (`metatheory/Dregg2/Circuit/Emit/DerivationRung2.lean:180`) |

`TinyAutomataCompose.lean` holds `costOf`/`DescCost` (the cost record these pins read),
`TinyAutomataSatisfiable.lean` the product-first witnesses, `TinyAutomataPacked.lean` the packed variant,
`DfaRoutingSubsetTableCost.lean` the table-routing refinement over the cheaper multiplicity-carrying
table acceptance.

## What these do not do

- None of the routing or replay theorems binds the word to a content commitment `c`; only the abstract
  `Dfa.lean` statement does (`docs/automata/01-dfa.md` §4). Restating each `*_refines_classify` with the
  `c` conjunct and the splice falsifier is the program's milestone (SUBSTRATE-DECISION §5 item 2).
- The weld is over binary symbols (`ASYM = 2`), so a byte costs 8 rows of 16 chip permutations each.
- The Dyck grammar's language is finite at the deployed depth (at most 6 tokens).
