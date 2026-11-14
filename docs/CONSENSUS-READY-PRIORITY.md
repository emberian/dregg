# Shared finality ready priority

Behavior: each anchor contributes a Kahn linearization of its approved, enrolled
closure difference. Among currently ready blocks, choose the lexicographically
least `(round, sequence, creator bytes, source block id)`. Causal readiness takes
precedence over every component, including round: an enrolled block can have a
higher-round ancestor through an unenrolled relay.

This is a consensus-order change. `tau`, `tau_with_config`, `tau_unified`, and
constitution wrappers share this priority. The node's Rust fallback and shadow
comparison therefore change order within anchor segments, as does multi-member
committee replay through that same projection. Anchor selection,
segment membership, enrollment, and equivocation predicates are unchanged.

The tuple is total for distinct content-addressed blocks. Given its round, all
remaining components are properties of the block. Arrival order, HashMap order,
and participant-list positions cannot break ties. Participant-list order still
selects leaders; it is deliberately not the ordering of creator bytes.

## Representation agreement

`VerifiedFinality::build_wire` assigns integer ids by sorting
`(sequence, creator bytes, source block id)`. The last component is necessary for
equivocating twins. Lean's explicit lexicographic `(round, sequence, integer id)`
comparison therefore represents the same order as Rust's four-component tuple.
An integer rank can shift when the lace grows, but the comparison of any two held
blocks cannot. The wire grammar is unchanged; twin-containing wires acquire a
canonical id assignment.

The Rust ordering projection now stores skeletons under the original source ids.
Rehashing their reduced payloads both changed tie-breaks and could collapse two
source blocks (for example, equal bytes carried by different payload variants).
`insert_ordering_projection` is an explicitly unverified projection API, like
`insert_unverified`: it checks causal closure, not authentication. It must receive
already-authenticated source blocks. The network admission path is unchanged.
Source block hashes, signatures, serialized block formats, and receipt formats
do not change. Executed turn order and thus resulting state roots can change.

## Proof boundary and regression coverage

`readyBefore_total` proves totality of the priority.
`xsortWith_perm`, `xsortBy_perm`, `xsortWith_linear_extension`, and
`anchorSegment_linear_extension` quantify over the priority's key lace; their
permutation and causal guarantees do not depend on key values. Existing
red/green traces remain, with additional traces separating round, sequence and
id priority. `TauPrefixMonotone` continues to use closure stability.

`anchorSegment_excludes_covered_ancestors` proves the cross-segment exclusion
step under predecessor-closed coverage. `TauOrderCausal` remains the stated
whole-order obligation: deriving closed coverage along the actual anchor-chain
fold is still needed for the unconditional DAG theorem. The patch does not
claim that the new lemma completes that proof.

Rust's `ready_priority_is_round_sequence_creator_source_id` separates each tuple
component, checks opposite input orders, and makes readiness defeat priority.
`wire_ids_break_equivocating_twins_by_source_id` starts with twins in descending
source-id order, so deleting the final comparison deterministically fails. It
also checks that projection retains both identities despite equal reduced
payload bytes. The node differential compares exact source-id sequences for
round-synchronous committees, a late joiner, and a relay; coordinate equality
alone is insufficient for twins.

Lean source in the FFI closure changes, so a new source-matched archive/seed key
is required. An old archive is not evidence about this rule.

## Validation

The final hbox Lean build passed for `Dregg2.Distributed.BlocklaceFinality`,
`Dregg2.Consensus.TauPrefixMonotone`, and all ten direct distributed importers.
All builds used the isolated copy, `SWARM_MEM_MAX=32G`, and
`LEAN_NUM_THREADS=4`. The Linux x86_64 / Lean 4.35 source key is
`9dcff65eea4f115d`.

Four local, individually filtered `dregg-blocklace` tests passed:
`ready_priority_is_round_sequence_creator_source_id`,
`test_tau_differential_against_lean_model`,
`test_concurrent_blocks_deterministic_tiebreaker`, and
`test_tau_unified_external_blocks_dont_inflate_rounds`.
They use unsigned ordering fixtures and need no native crypto. The absent Mac
archive caused the build script to explicitly skip Lean compilation; these
results are not archive-backed differential evidence.

The strict hbox command for
`the_two_orders_the_node_swaps_between_agree_exactly` completed with exit status
0. Before execution, the build recorded source provenance for 347 Dregg2 archive
members; the test was observed running with `DREGG_TEST_REQUIRE_LEAN=1`.
However, both the isolated build directory and the supplied warm source clone
were removed externally while the test was running. The final test-summary log
was lost. Record this as successful command completion with incomplete retained
evidence, not as a fully captured native verification run.

Still required on a restored source-matched Linux archive:

- Re-capture `the_two_orders_the_node_swaps_between_agree_exactly`.
- Run `the_verified_order_survives_a_late_joiner_and_a_relay` (now exact-sequence).
- Run `wire_ids_break_equivocating_twins_by_source_id` in the node library target.

The native run used `CARGO_TARGET_DIR=./target-dep`, `CARGO_BUILD_JOBS=4`,
`DREGG_TEST_REQUIRE_LEAN=1`, `DREGG_LEANC_JOBS=4`, `LEAN_NUM_THREADS=4`, and
`SWARM_MEM_MAX=32G` under `swarm-build`. `DREGG_LEAN_FFI_NO_ARCHIVE_GC=1`
retained the full archive; it did not disable provenance or required-export gates.
No Lean build ran on the Mac. No commit or push was made.
