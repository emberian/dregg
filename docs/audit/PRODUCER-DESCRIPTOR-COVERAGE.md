# PRODUCER ≡ DESCRIPTOR COVERAGE (census R3)

**The structural blind spot.** The drift gate (D2) proves *Lean-emit ≡ committed-JSON*. It does **not**
prove *producer ≡ committed-descriptor* — that the Rust trace producer emits a trace whose
shape/host-constants match the descriptor the light client verifies against. That equation lives
**only** in whatever prove+verify roundtrip coverage exists. `be732a9dd` (the v13 stale wide-descriptor
catch) proved this diverges **silently**: 7 wide members laid their AFTER carrier chain at a stale base
while the honest producers read the v13 base, so `verify` failed on *honest* turns — a class the drift
gate cannot see. Census `TRUST-BASE-CENSUS.md §6 R3` named this structural.

**This document** enumerates every deployed descriptor member of the three committed registries and
classifies each member's producer≡descriptor coverage as **COVERED** (a real, non-`#[ignore]`
prove+verify roundtrip against that registry's committed descriptor), **PARTIAL** (parsed/shape-checked,
or a roundtrip exists but is `#[ignore]`d behind a *named* seam), or **UNCOVERED** (no roundtrip — the
silent-divergence risk). The machine-checked ledger + the anti-regression gate live in
`circuit/tests/producer_descriptor_coverage_gate.rs`.

## Summary

| Registry (file) | Members | COVERED | PARTIAL | UNCOVERED | Completeness gate |
|---|---:|---:|---:|---:|---|
| **v3-live** (`rotation-v3-staged-registry.tsv`) — the CURRENTLY-DEPLOYED 1-felt registry | 58 | 25 | 10 | 23 | `producer_descriptor_coverage_gate::v3_registry_every_member_classified` (**new**) |
| **bare-wide** (`rotation-wide-registry-staged.tsv`) — STAGED 8-felt (the v13-affected surface) | 57 | 35 | 2 | 20 | `producer_descriptor_coverage_gate::wide_registry_every_member_classified` (**new**) + `wide_completeness_ledger::provability_scoreboard_deployed_wide_path` (existing) |
| **umem-welded** (`rotation-wide-umem-welded-registry-staged.tsv`) — STAGED welded | 57 | 17 | 27 | 13 | `wide_umem_weld_matrix_gauntlet::matrix_enumerates_all_57` (existing) |

The UNCOVERED counts are dominated by the **cap-write / cap-open family**, which is uncovered *by
design*: on the bare (sovereign) producer these effects are forbidden / UNSAT and their light-client
route is the cap-open path — whose non-turn-bound prove-through is itself `#[ignore]`d behind a *named*
shared Rust handoff (the IR-v2 cap-node lookup multiplicity reconciliation gap). Only
`transferCapOpenTBVmDescriptor2R24` is green on the cap-open path.

## The live R3 probes (this audit's fresh coverage)

Two deployed **v3-live** members had **zero** prove+verify roundtrip anywhere on the live path — they
appeared only in the STAGED wide/welded SDK gauntlets, never against the committed 1-felt V3 descriptor:

- `cellUnsealVmDescriptor2R24`
- `cellDestroyVmDescriptor2R24`

`producer_descriptor_coverage_gate::cell_{unseal,destroy}_v3_producer_descriptor_roundtrip` now drive
each producer trace through `prove_vm_descriptor2` + `verify_vm_descriptor2` against the committed V3
descriptor. **Result: both GREEN** — the producer's shape matches the committed descriptor. The gap was
*benign* (these ride the shared generic-base producer, well-exercised by transfer/burn/cellSeal), but it
was a real zero-coverage hole and is now closed with a genuine roundtrip. **No live producer/descriptor
mismatch (v13 class) was found in the probed members.**

## The ranked UNCOVERED / PARTIAL set (the silent-divergence risk, by producer distinctness)

The v13 divergence class = a member with a **distinct / special producer path** whose producer≡descriptor
is not roundtrip-verified. Ranked by how much a member's producer diverges from the well-tested generic
base:

1. **`heapWriteVmDescriptor2R24` — PARTIAL on BOTH v3-live and bare-wide (highest priority).** A
   **distinct heap-splice producer** (`generate_rotated_heap_write_*`), structurally pinned only
   (`heap_write_deployed_root_forced` parses + checks the `.write` map_op; `wide_new_members_cover` pins
   the 16 wide-commit PIs) — **no end-to-end prove+verify roundtrip** against either committed
   descriptor. This is the sharpest surviving analog of the v13 finding: one of the exact 7 special
   members v13 hit, with a distinct producer and no roundtrip on the deployed path. **Recommended next
   probe.**
2. **`customVmDescriptor2R24` — PARTIAL on v3-live.** Proves on the wide path
   (`wide_completeness_ledger::custom_proves_on_deployed_wide_path`); the deeper V3 per-turn `proofBind`
   roundtrip is gated (`custom_binding_*` `#[ignore]`d). Distinct recursion-bound producer.
3. **`setFieldVmDescriptor2-0R24 … -7R24` (8) — PARTIAL on v3-live.** The vk_epoch_value setField
   roundtrip is `#[ignore]`d behind a *named* seam: the V1 setField producer does not yet fill the
   written-slot value8. A **documented producer-incompleteness** — exactly the R3 class, but named and
   burning down (the v13 value8 completion lane), not silent. Covered on bare-wide (scoreboard).
4. **The cap-open family (`*CapOpen*`, ~17 on v3-live) — UNCOVERED.** Distinct widen producers; the
   non-TB prove-through is `#[ignore]`d behind the shared IR-v2 cap-node lookup handoff. A test *exists*
   (ignored) → the divergence would be caught when the seam closes; lower silent-risk, but no green
   producer≡descriptor roundtrip on the deployed path today.
5. **The bare cap-write family (`attenuate`/`grantCap`/`revoke`/`refresh`/`introduce`/`revokeCapability`,
   6 on v3-live; named residual on bare-wide) — UNCOVERED by design.** Forbidden / UNSAT on the bare
   producer; route = cap-open. `wide_completeness_ledger` *asserts* this is the exact named
   unprovable-on-wide set (a positive gate on the residual).

Everything else on v3-live and bare-wide is COVERED by a real roundtrip (see the ledger in the gate
file for the per-member test pointer).

## umem-welded registry lanes (existing gate `matrix_enumerates_all_57`)

The welded registry already has an EXACT-completeness gate. Its lanes map to coverage strength:

- **`HereGreen` (8) → COVERED.** Genuine mint → wire-verify GREEN via `mint_and_wire_verify`
  (`prove_wide_umem_welded_staged` → `verify_effect_vm_rotated_with_cutover`): the domain-1 record-pin
  family (setPerms, setVK, cellSeal, cellUnseal, cellDestroy, receiptArchive, refusal, makeSovereign).
- **`SiblingCovered` (9) → COVERED (caps plane).** Proven end-to-end by a sibling gauntlet asserting
  `ops[0].domain == Caps` (the cap-open write family + spawn).
- **`ValueOrGrowGate` (27) → PARTIAL.** "Covered by its own gauntlet (transfer) **or pinned
  structurally** by `wide_umem_weld_registry_parity_and_no_narrowing`." The structurally-pinned subset
  (setField-0..7, the grow-gate births, heapWrite, supplyMint, transferCapOpenTB, …) is PARTIAL — no
  per-member welded roundtrip; the weld is a byte-parity check over the bare-wide twin.
- **`Forbidden` (13) → UNCOVERED-by-design.** Wire-rejected authority/plain-cap descriptors; only
  `grantCapVmDescriptor2R24`'s rejection is empirically tested
  (`matrix_forbidden_plain_cap_is_wire_rejected`); the other 12 are classified, not individually
  wire-rejection-tested.

## The methodology fix (the coverage gate)

`circuit/tests/producer_descriptor_coverage_gate.rs` closes the structural blind spot:

- `v3_registry_every_member_classified` and `wide_registry_every_member_classified` assert **exact
  completeness**: every deployed member of the v3-live and bare-wide registries (which had no
  per-member coverage gate) must appear in the coverage ledger with a Covered(test) / Partial(seam) /
  Uncovered(reason) classification. **A new deployed descriptor member with no classification FAILS the
  build** — the producer≡descriptor question can never again silently open for a new member. (The gate
  already caught a bug during authoring: two stale ledger keys —
  `refreshDelegation`/`revokeDelegationVmDescriptor2R24` — that are not real V3 members.)
- The umem-welded registry is already gated by `matrix_enumerates_all_57`; the new gate names it as the
  third registry so the three-registry surface is jointly closed.

**Remaining recommendation (not scaffolded — needs producer work in another lane):** upgrade the ledger
from *classification* to *enforced roundtrip pointer* for the PARTIAL set — most valuably a real
`heapWrite` end-to-end roundtrip (v3-live + bare-wide) and the setField value8 completion, retiring the
two sharpest PARTIAL entries. The gate structure already reserves the `Covered(test)` slot for them.
