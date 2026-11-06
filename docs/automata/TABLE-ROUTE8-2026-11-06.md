# Initiative 1 — ordered table routes at eight lanes

Register row **#1 — parser/language excellence**. Owner: Codex gpt-6-astra table-binding lane,
2026-11-06. This is a lane report; the deputy report and landing SHAs belong to the root.

[READ] The legacy `dregg-dfa-routing-table::exact-public-v1` proves a legal trail through the
exact declared transition multiset. Its two endpoint PIs do not identify a word. The two-loop
witnesses in `DfaRoutingTableBound` accept both `[1,2]` and `[2,1]`. The file's former phrase
“complete public-data characterization” was too strong: its theorem is a necessary condition,
not a construction of every satisfying trace. That wording is corrected.

[MEASURED] `DfaRoutingTableRoute8.demoBoundDesc` is now Lean-emitted as
`dregg-dfa-routing-table::route8-bound-v1` on the same two-loop table. The generated artifact
has 20 main columns, 11 PIs, 32 constraints and two tables. The legacy base has 3 columns,
2 PIs, 4 constraints and one table. The delta is **17 columns, 9 PIs, 28 constraints and
one wide permutation per row**. A 4,096-byte byte-symbol record therefore adds 4,096
permutations. No hand-written Rust AIR constraints were added. The emitted JSON SHA-256 is
`8b47d815683064ee69a5f618e8de4fddcbab8e2456d561bd4a09b4bc646f9c6e`.

The common `RouteChain8` decorator appends predecessor8, output8 and a one-based index.
Every row absorbs `[domain,index,current,symbol,next,predecessor8,0,0,0]`; its 13 meaningful
inputs are padded to the chip's admitted arity 16. Arity 13 itself is forbidden by the deployed
chip. All eight output lanes are published and threaded. Table routing uses a fixed zero seed;
the attested weld reuses the same helper with the authenticated root8 seed and a distinct domain.
The caller-selected descriptor commits the **declared transition table**, which may be a run
multiset rather than a complete automaton table. The demo separately checks those declared rows
against its signed policy table.

[MEASURED] Warm single-file Lean checks passed for `RouteChain8`, `RouteChain8Binding`,
`RouteChain8Refine`, `RouteChain8Canonical`, `DfaRoutingTableRoute8` and the complete
`DfaRoutingTableRoute8Bound` witness and strengthened public theorem. Their refinements preserve every base constraint
and memory/map log, extract the full eight-lane row hash, prove the counter and public length
from AIR constraints, and prove the public route equals the ordered payload fold. The binding
reduction has no global hash-injectivity premise: unequal runs force a deterministic named
collision whose two inputs belong to those actual runs. Fixed payload widths rule out encoding
aliases before the cryptographic argument. Honest self-runs refute the collision branch without
any hash assumption. Kernel-evaluated examples exercise both the order-splice and actual-collision
branches. `RouteChain8Canonical` additionally proves the named inputs have canonical field
representatives and arity 16; canonical record payloads and canonical full-width hash outputs
exclude modular aliases from the operational collision statement. Critical axiom sets are pinned with `#guard_msgs` and contain only the standard three.

The runtime module `circuit/src/route_chain8_witness.rs` supplies witness construction and the
`verify_route8` acceptance wrapper. The wrapper checks the proof's first/main `degree_bits`
height against the public length, rejects height zero, overflow and height at least the field
characteristic, then runs the ordinary descriptor verifier. This checks the refinement's
no-wrap premise using the proof's actual height, rather than trusting a producer assertion.
The witness constructor validates all shapes before mutation.

[READ] The initial shape has **no inactive padding rows**. Witness construction explicitly
requires a power-of-two row count; arbitrary-length records need a separate active-row/padding
shape. This is the same limitation the exact-public absence receipt already carried. Exact-public
lookups still require the declared transition multiset to match usage exactly. The full-width
`ChipTableSoundN` premise and model-to-STARK soundness boundary remain named; this work does not
claim to remove them.

Integration checks pending at report creation: filtered deployed Rust tests (`table_route8_served`, weld and absence receipt), source-closure
provenance restamp, and the root's batched bb2 whole-tree build. No remote jobs were started
by this lane. The root owns the shared build allocation and commits.

[MEASURED] The final `bound_word_or_collides` and `bound_classifies_or_collides` checks passed
with their exact axiom pins. Their `RecordCollision` contains the full-output inequality/equality,
canonical arity-16 input blocks, and membership in the actual trace and deterministic record
computations. `witness_bound_classifies` applies this strengthened theorem to a complete accepted
two-row AIR witness. `order_splice_weak_accepts`, `order_splice_strong_refuses` and
`length_splice_strong_refuses` supply independent order and length separators.

Files owned by this lane: `metatheory/Dregg2/Circuit/Emit/{RouteChain8,RouteChain8Binding,
RouteChain8Refine,RouteChain8Canonical,DfaRoutingTableRoute8,DfaRoutingTableRoute8Bound}.lean`,
the legacy `DfaRoutingTableBound.lean` explanatory correction, `circuit/src/route_chain8_witness.rs`,
its module declaration in `circuit/src/lib.rs`, both new route registrations in
`circuit/src/descriptor_by_name.rs`, `circuit/tests/table_route8_served.rs`, the table-route8
by-name JSON, and this note. The weld owner supplies its JSON and Lean instance; the emitter
owner supplies both `EmitByName.lean` rows. The demo owner switched its consumer to this shared
constructor and height-checking verifier.

No engineering choice here needs ember's approval. The next shape work is arbitrary logical
length without pretending zero-byte padding belongs to the record. A shared active-row extension
must preserve the digest on inactive rows, count only active rows, and classify only the active
prefix; the current ungated chip lookup cannot simultaneously force `out=H(input)` and
`out=previous` on inactive rows without a separate raw digest or a guarded lookup. The table
lookup likewise needs explicit inactive-row semantics. Until those gates and their refinement
exist, the public API refuses unsupported heights.

[READ] The direct `verify_route8_record` consumer now recomputes the selected record's initial
and final states, full eight-lane route and exact length before verifying the proof. Its step
callback returns errors for an invalid policy lookup. Table and weld tests reuse the same proof
and public inputs while substituting the external record; no PI mutation stands in for that test.
`verify_route8` remains the lower-level public-statement checker. Native execution is queued.
