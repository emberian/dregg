# The faithful state commitment (v9→v11) & the cap-write keystones

What this IS at HEAD. The cross-cutting campaign that widened every Merkle-root
component of the deployed rotated state commitment from lossy ~31-bit 1-felt folds
to faithful **8-felt (~124-bit)** — matching the system's own ~130-bit FRI/STARK
soundness floor — and then closed the **cap-write family**: every cap-writing
effect now rides a shape-matched, circuit-forced keystone descriptor. The law
itself is [`docs/FAITHFUL-COMMITMENT-LAW.md`](../FAITHFUL-COMMITMENT-LAW.md); this
page grounds the deployed realization at file:line. Every load-bearing claim below
is cited to Rust file:line or a Lean `Module.decl`.

Companions: [`circuit.md`](circuit.md) (the prove/verify crates),
[`cells.md`](cells.md) (the cell-side commitment), [`lean-circuit.md`](lean-circuit.md)
(the soundness apex the keystones feed).

## Geometry — the v9 → v10 → v11 growth

| Const | Value | Location |
|---|---|---|
| `NUM_PRE_LIMBS` | **169** | `circuit/src/effect_vm/trace_rotated.rs` |
| `V9_NUM_PRE_LIMBS` | **169** (cell-side twin) | `cell/src/commitment.rs` |
| `B_SPAN` | **227** | `circuit/src/effect_vm/trace_rotated.rs` |
| `N_ROT_SITES` / `GRAD_ROT_WIDTH` | **128** / **1581** | `circuit/src/effect_vm/trace_rotated.rs` |
| `WIDE_NUM_CARRIERS` / `WIDE_WIDTH` | **57** / `GRAD_ROT_WIDTH + 912` | `circuit/src/effect_vm/trace_rotated.rs` |
| `CHIP_RATE` | **16** | `circuit/src/descriptor_ir2.rs:279` |
| `CHIP_NODE8_ARITY` | **16** | `circuit/src/descriptor_ir2.rs:302` |

The path: `37 (v9) → 67 (v10: +30 faithful completion limbs 37..66 — perms/vk/
cap/heap/fields-root lanes 1..7) → 88 (v11: +21 dedicated accumulator completion
limbs 67..87) → 112 (v12: +24 carrier-material octets 88..111) → 169 (v13: +56
flat-fields[0..7] completion lanes 112..167 + 1 pad limb 168 — the faithful
`field_limbs8` octet closing the LAST degraded felt)`; `B_SPAN 51 → 91 → 119 →
151 → 227`.

## The node8 primitive — ONE hash gadget under all six roots

The shared arity-16 compression `perm(L8 ‖ R8)[0..8]` (8-felt in, 8-felt out, no
tag lane, no lane-0 squeeze):

- **Rust**: `cap_node8` (`circuit/src/cap_root.rs:148`; `CAP_DIGEST_W = 8`,
  `cap_root.rs:133`; `CanonicalCapTree` with 8-felt levels, `cap_root.rs:312`);
  `heap_node8` (`circuit/src/heap_root.rs:458` — "IDENTICAL compression to
  `cap_root::cap_node8` — cap/heap/fields share this ONE node8 lane",
  `heap_root.rs:453`; `HEAP_DIGEST_W = 8`, `:440`; `CanonicalHeapTree8`, `:617`;
  `compute_canonical_heap_root_8`, `:512`; `recompose_membership_8`, `:579`).
- **Chip realization**: the node8 lookup tuple `[16, L8, R8, out8]`
  (`circuit/src/descriptor_ir2.rs:1823`), all 8 output lanes bound
  (`CHIP_OUT_LANES = 8`, `descriptor_ir2.rs:1929`), boolean-gated selector
  (`descriptor_ir2.rs:1950`, `:2393-2410`).
- **Lean**: the width-agnostic Merkle spine `CapMerkleGeneric` (`StepG`
  `CapMerkleGeneric.lean:30`, `recomposeG` `:39`, the injectivity keystone
  `recomposeG_inj_of_path` `:51`) instantiated by the 8-felt schemes:
  `Cap8Scheme` (`DeployedCapTree.lean:637`), `nodeOf8` (`:667` — "BYTE-IDENTICAL
  to `cap_root.rs::cap_node8`"), **`nodeOf8_injective`** (`:679`,
  `#assert_axioms` at `:934`), `heapNodeOf8_injective`
  (`DeployedHeapTree.lean:71`), `fieldsNodeOf8_injective`
  (`DeployedFieldsTree.lean:75`). The CR carrier is `Compress8CR`
  (`DeployedCapTree.lean:630`) — a Prop hypothesis, never an axiom.

## The six roots — deployed keystone descriptors + apex pins

Each root's write is FORCED by a shape-matched after-spine/insert descriptor whose
`Rfix` position the assembled apex quantifies over (registry `v3RegistryHeap`,
`metatheory/Dregg2/Circuit/CircuitSoundnessAssembled.lean:139`, length 59 `:254`):

| Root | Keystone descriptor | Shape | Keystone theorem | Apex pin |
|---|---|---|---|---|
| cap_root | `effCapOpenWriteV3` / `effCapInsertV3` / `effCapRemoveV3` (`CapOpenEmit.lean:585/:661/:680`) | update / insert / remove (next section) | `effCapOpenWriteV3_forces_write8` (`CapOpenEmit.lean:1903`) + the insert/remove twins | `Rfix 12` (attenuate) + the family pins below |
| heap_root | `effHeapWriteV3` (`HeapOpenEmit.lean:386`) | update-at-key | `heapOpen_writesTo8` (`HeapOpenEmit.lean:222`) | `Rfix 56`, pos 45 (`CircuitSoundnessAssembled.lean:258`) |
| fields_root | `effFieldsWriteV3` (`FieldsOpenEmit.lean:369`) | update-at-key | `fieldsOpen_writesTo8` (`FieldsOpenEmit.lean:217`) | `Rfix 39`, pos 55 |
| nullifier_root | `effAccumInsertV3` … `(some SEL_NOTE_SPEND)` | sorted-INSERT | `accumInsert_writesTo8` (`AccumulatorInsertEmit.lean:117`) | `Rfix 27`, pos 56 (`CircuitSoundnessAssembled.lean:227`) |
| commitments_root | `effAccumInsertV3` … `none` | sorted-INSERT | + `accumInsert_writesTo8_setGrows` (`:134`) | `Rfix 28`, pos 57 (`:236`) |
| cells_root | `effAccumInsertV3` … `none` | sorted-INSERT | (same keystone) | `Rfix 17`, pos 58 (`:245`) |

`#assert_axioms` on the insert pins at `CircuitSoundnessAssembled.lean:755-757`;
the capstone footprint is ⊆ `{propext, Classical.choice, Quot.sound}` (`:83`).

### The INSERT-shaped accumulator keystone

`effAccumInsertV3` (`AccumulatorInsertEmit.lean:232`) is INSERT-shaped, not
update-shaped: the before-root opens a genuine **non-membership bracket** (the
sorted-tree gap witness) and the after-root is the **spliced membership** — the
twin pair `nonMembership_sound8` (`SortedTreeNonMembershipHeap8.lean:149`,
`#assert_axioms` `:184`) + `update_sound8` (`:164`). Trace-forced consumers:
`effAccumInsertV3_forces_afterMembership` (`AccumulatorInsertEmit.lean:307`),
`effAccumInsertV3_forces_write8` (`:361`).

**The selector-gated KEY/VALUE binds** (the noteSpend residual close): the bind
combinator `bindGateI` (`AccumulatorInsertEmit.lean:183`) takes `sel : Option Nat`
— `none ⇒` the unconditional `eqGate`, `some s ⇒ sel·(leaf−col) = 0` (active on
the firing row, vacuous on padding); `keyBindGateI` `:207`, `valueBindGateI`
`:212`, forced by `bindGateI_forces` `:191`. noteSpend instantiates
`some SEL_NOTE_SPEND` (`CircuitSoundnessAssembled.lean:233`) because its
`valueCol = NOTE_VALUE_LO` is per-row economically constrained (must be 0 on
padding — irreconcilable with an unconditional per-row bind); noteCreate /
createCell pass `none` (`:242`, `:250`). MEMBERSHIP + rootPin welds stay
unconditional in all three.

### The Rust producers (the genuine node8 fill)

The rotated trace producers fill genuine `CanonicalHeapTree8::root8()` — never a
lane-0 squeeze, never a `[x; 8]` replicate — into both rotated blocks:

- nullifier: lane 0 = limb 26 ‖ lanes 1..7 = limbs 67..73
  (`circuit/src/effect_vm/trace_rotated.rs:1094-1110`);
- cells: lane 0 = limb 0 ‖ 81..87 (`trace_rotated.rs:1192-1207`);
- commitments: lane 0 = limb 27 ‖ 74..80 (`trace_rotated.rs:1272-1287`);
- cap: 25 ‖ 51..57, heap: 28 ‖ 58..64, fields: 36 ‖ 65,66,19..23, authority
  digest: 24 ‖ 12..18, perms: 33 ‖ 37..43, vk: 34 ‖ 44..50 — the cell-side twin
  is `compute_rotated_pre_limbs` (`cell/src/commitment.rs:968-1069`).

## The cap-write family close — all 8 cap-writing effects on shape-matched keystones

**The root cause (a liveness break, not a soundness break):** the heap-8-felt
migration made the witness heaps `CanonicalHeapTree8`
(`circuit/src/heap_root.rs:617`), which made every scalar **arity-2 cap map-op
shape-UNSAT for an honest prover** ("the arity-2 scalar map-op is GONE from the
WRITE-bearing wrappers (shape-UNSAT against the native-8-felt witness heaps)",
`sdk/src/full_turn_proof.rs:7111`). Compounding it, `writesTo8` was UPDATE-at-key
only — it covered attenuate but no effect that *changes the cap key-set*
(commit `48d981698`: "delegate/introduce/delegateAtten INSERT a fresh cap key;
revokeDelegation REMOVEs one — both change the cap key-set, no shared
before/after path"). The gap went unnoticed while the SDK test suite carried 7
`E0308` compile breaks lagging the same migration (commit `5ea008aab` — "the
big-bang `--tests` check was truncated by a disk-full moment"), so the cap-write
proving paths were not being exercised. The close: two new keystone shapes
(INSERT, REMOVE) + the existing UPDATE after-spine, and all 8 effects rewrapped.

| Effect | Wrapper (all in `CapOpenEmit.lean`) | Keystone | Rfix pin (`CircuitSoundnessAssembled.lean`) |
|---|---|---|---|
| delegate | `delegateWriteCapOpenV3` (`:738`) | `effCapInsertV3` | `Rfix 1`, pos 46 (`:498`) |
| introduce | `introduceWriteCapOpenV3` (`:690`) | `effCapInsertV3` | `Rfix 10`, pos 47 (`:507`) |
| delegateAtten | `delegateAttenWriteCapOpenV3` (`:778`) | `effCapInsertV3` | `Rfix 11`, pos 48 (`:510`) |
| spawn | `spawnWriteCapOpenV3` (`:753`) | `effCapInsertV3` | `Rfix 19`, pos 52 (`:532`) |
| revoke / revokeDelegation | `revokeDelegationWriteCapOpenV3` (`:701`) | `effCapRemoveV3` | `Rfix 2` / `Rfix 14`, pos 49 (`:503`, `:513`) |
| revokeCapability | `revokeCapabilityWriteCapOpenV3` (`:716`) | `effCapRemoveV3` | ⚠ `Rfix 24` still pins the authority-only `revokeCapabilityCapOpenV3` (`:525`) — see residuals |
| attenuate | `attenuateCapOpenEffV3` (`:812`) | `effCapOpenWriteV3` | `Rfix 12` |
| refreshDelegation | `refreshDelegationWriteCapOpenV3` (`:726`) | `effCapOpenWriteV3` | `Rfix 55`, pos 50 (`:518`) |

The three shapes:

- **INSERT** (`effCapInsertV3`, `CapOpenEmit.lean:661` = `effCapOpenV3` + the 8
  AFTER cap-root welds `afterCapRootWelds` `:648`): keystones `capInserts8`
  (`CapInsertEmit.lean:80`), **`capInsert_writesTo8`** (`:123` — genuine
  `nonMembership_sound` bracket + `MembersAt8` afterRoot + `update_sound`),
  `capInsert_writesTo8_setGrows` (`:140`), trace-forced
  `effCapInsertV3_forces_afterMembership` (`:237`) /
  `effCapInsertV3_forces_write8` (`:274`). The Rust witness is
  `CanonicalCapTree::insert_witness` (`circuit/src/cap_root.rs:768`) — fail-closed
  on sentinel/present key, pred/succ non-membership bracket, `debug_assert`
  recompose = rebuilt root.
- **REMOVE** (`effCapRemoveV3`, `CapOpenEmit.lean:680` = base + the 8 BEFORE
  welds `beforeCapRootWelds` `:669`): keystones `capRemoves8`
  (`CapRemoveEmit.lean:77` — tombstone zero-fold via `sortedRemove`),
  **`capRemove_writesTo8`** (`:120`), `capRemove_writesTo8_setShrinks` (`:137`),
  `effCapRemoveV3_forces_write8` (`:268`). Rust:
  `CanonicalCapTree::remove_witness` (`cap_root.rs:818`) — BEFORE membership
  path, then `new_root = recompose_membership(CAP_ZERO8, …)` — the tombstone
  zero-fold (`:834`), matching the cell-side tombstone semantics
  ([`auth.md`](auth.md) revocation section).
- **UPDATE** (`effCapOpenWriteV3`, `CapOpenEmit.lean:585`, defined in the
  §12-relocated block at `:504`): the arity-7 after-spine — §11
  (`CapOpenEmit.lean:1747-1820`) is the pure keystone (two node8 spines sharing a
  path), §12 (`:1821-1990`) the wiring (`effCapOpenWriteV3_afterCore` `:1841`,
  `effCapOpenWriteV3_forces_write8` `:1903`, `#assert_axioms` `:1989-1990`).

**Rust routing**: `build_effect_vm_cap_open_leg` (`sdk/src/full_turn_proof.rs:2845`)
branches by shape — `attenuate_after_spine` (`:2898`, attenuate + refresh),
`insert_after_spine` (`:2915`, delegate/introduce/delegateAtten/spawn),
`remove_after_spine` (`:2936`, revokeDelegation + revokeCapability). The
effect-kind → route table is `cap_open_route_for_run`
(`sdk/src/full_turn_proof.rs:2149`); the light-client verify allow-list is
`turn/src/executor/proof_verify.rs:137-153`. Descriptor regen (`824c2963e`,
`136de6281`, `bae447985`) re-pinned the three registries
(`circuit/descriptors/rotation-v3-staged-registry.tsv` + wide + umem-welded); the
arity-2 map-op `_forces_write` theorems were deleted as shape-UNSAT (`6a7283580`).

**Teeth**: witness unit teeth in `circuit/src/cap_root.rs` —
`insert_witness_recomposes_rebuilt_root_and_brackets` (`:1015`),
`remove_witness_matches_tombstone_root` (`:1054`),
`revocation_witness_rejects_fabricated_slot` (`:1325`),
`membership_witness_rejects_forged_leaf` (`:1406`),
`sparse_matches_dense_at_depth_16` (`:1556`). Prove+verify leg tests in
`sdk/src/full_turn_proof.rs` — delegate `:9020`, introduce `:9409`,
delegateAtten `:9661`, spawn `:9448`, revokeCapability route `:8085`, refresh
`:8296`; the no-silent-forge REMOVE tooth
`write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge`
(`:7124`); the forge-masked harness `run_insert_after_spine_prove_verify_forge_masked`
(`:8600`); domain-2 gauntlets `sdk/tests/wide_umem_weld_domain2_siblings.rs`,
`sdk/tests/wide_umem_weld_matrix_gauntlet.rs:554-565`.

## The standalone DSL-p3 cap-membership leg (8-felt, no lane-0)

The standalone DSL-AIR cap-membership leg binds the GENUINE 8-felt cap_root:
`ConstraintExpr::MerkleHash8 { output_cols[8], left_cols[8], right_cols[8] }` —
the multi-output node8 gadget in `circuit/src/dsl/dsl_p3_air.rs` (input state
`L8 ‖ R8` seeded into all 16 lanes, byte-identical to `cap_node8`,
`dsl_p3_air.rs:356-367`; **all 8 genuine permutation output lanes bound — "NOT
eight copies of lane 0"**, `dsl_p3_air.rs:575-586`). The leg is
`circuit/src/dsl/cap_membership.rs` (`cap_membership_circuit_descriptor` `:91`,
the `MerkleHash8` fold `:133`, descriptor `"dregg-cap-membership-dsl-v2-node8"`
`:200`) with a **16-felt PI vector `[leaf_digest(8) ‖ cap_root(8)]`**
(`cap_membership.rs:206`); the SDK emits and re-verifies it at 16 PIs
(`sdk/src/full_turn_proof.rs:792` §5b).

## The CI gate (the law's enforcement)

`.ast-grep/rules/faithful-commitment-felt.yml` carries exactly two rules:
`degraded-felt-commitment` (`:23` — the `fold_bytes32_to_bb($_)` patterns) and
`replicated-felt-commitment` (`:62` — the `[$X; 8]` replicate, with
`[0;8]`-style constants excluded). `scripts/check-no-degraded-felt.sh` runs them
over the commitment producers with an inline `// ast-grep-ignore` allowlist;
[`docs/FAITHFUL-COMMITMENT-LAW.md`](../FAITHFUL-COMMITMENT-LAW.md) is the law text.

## Honest residuals (named, none hidden)

1. **`fields[0..7]` flat-record limbs — CLOSED (v13 fields-octet epoch).** The
   two producers (`cell/src/commitment.rs::compute_rotated_pre_limbs`,
   `turn/src/rotation_witness.rs::produce`) now emit the faithful
   `Faithful8::from_field_limbs8` 8-lane split (lane 0 at the welded limb `4 + i`,
   lanes 1..7 at the completion lanes `112 + 7·i .. +6`); the ast-grep allowlist
   directives are gone and the no-degraded-felt gate passes with zero fields
   entries. The shared value wrap freezes all 56 completion lanes on a value turn
   (`rotateV3FrozenAuthority_rejects_fields_forge`, `#assert_axioms`-clean); the
   ONE remaining in-circuit seam is the setField[0..7] WRITTEN slot's 7 completion
   lanes (the deliberately-gated **value8 weld** follow-on).
   **Deployed-vs-defined (2026-07-03 R1 audit — `circuit/tests/setfield_completion_lane_forge.rs`):**
   the DEPLOYED registry member (`EffectVmEmitRotationV3.lean:5363`) is
   `v3OfFrozen (setFieldTickFace slot)` — the freeze-**ALL** variant, which freezes
   the written slot's completion lanes too (before==after). The
   `fieldsCompletionFreezesExcept` / `setFieldV3` "except" variant is DEFINED and
   carries the value keystones but is NOT wired into the deployed cohort. So the
   deployed setField's high 224 bits are FROZEN to the pre-state (a forge of them is
   UNSAT — no ledgerless silent-forge), at the cost of an honest LARGE-value write
   being unprovable. The seam is therefore a **completeness** residual (the value8
   weld makes large writes provable AND declared-value-bound), not a soundness hole.
2. **The flat pre-limb twins zero-fill lanes 67..87** — the genuine accumulator
   node8 fill exists on the circuit trace-producer path (above), but the two
   flat-record producers (`cell/src/commitment.rs` `compute_rotated_pre_limbs`,
   `turn/src/rotation_witness.rs`) still carry the const-comment "zero-filled
   until producer-welded" (`commitment.rs:702`, `rotation_witness.rs:67`) — the
   nullifier/commitments roots enter them as 1-felt `hash_bytes`
   (`commitment.rs:1019`, `:1021`).
3. **`transferCapOpenTB` — the ONE load-bearing ~31-bit LC surface left.** The
   whole-image 8-felt digest flag-day FIRED long ago (`9e5a83935`, 2026-06-19):
   `compute_canonical_state_commitment_v9_felt8` (`cell/src/commitment.rs:1219`)
   IS the deployed end-to-end binding (producer `cipherclerk.rs:5750`, executor
   `proof_verify.rs:853` "the 1-felt waist is GONE", LC `full_turn_proof.rs:4217`);
   a stale header comment previously claimed otherwise (fixed at `:1213`). The
   1-felt `_v9_felt` (`:1187`) has test/bench callers only. What genuinely remains
   1-felt on the LC wire: `transferCapOpenTB` — the sole cap-open key with NO wide
   twin (the cohort weld refuses its multi-domain/turn-bound projection), so
   `full_turn_proof.rs:4285-4295` falls back to the 1-felt V3 registry for it
   alone (a reject tooth at `:4266-4272` bars the fallback for any key that HAS a
   wide twin). Closing it = the transferCapOpenTB wide-twin grind.
4. **The `Faithful8` type-wall** — a planned Rust newtype capstone (only
   constructor = the faithful conversions), named in
   `docs/FAITHFUL-COMMITMENT-LAW.md:84` and cross-referenced by the ast-grep rule
   (`faithful-commitment-felt.yml:46`). Not yet implemented. (Distinct from the
   *existing* Lean `DeployedFaithful8`, `DeployedCapTree.lean:730`.)
5. **`BUS_FACT` is not gone** — the node8 map-op chain rides its dedicated chip
   lanes, but the legacy arity-2 fact bus is still defined and active for the
   remaining scalar map-op chains (`circuit/src/descriptor_ir2.rs:335`, the
   `fact_bus.table_entry` at `:2551`).
6. **revokeCapability's apex pin lags its deployed route** — `Rfix 24` pins the
   authority-only `revokeCapabilityCapOpenV3` (pos 41,
   `CircuitSoundnessAssembled.lean:525`), while the deployed prover proves the
   REMOVE write wrapper whenever the node supplies the c-list witness, with a
   *named* authority-only fallback on an empty c-list
   (`sdk/src/full_turn_proof.rs:2331-2352` — "An empty c-list falls back to the
   authority-only `key` (named, not a silent forge)"). The Lean write wrapper +
   its `ClosureAll` rung exist (`revokeCapability_closedLog_capOpenSat`,
   `ClosureAll.lean:971`); moving the `Rfix 24` pin onto the write wrapper is the
   open apex-registry step.
7. **The terminal crypto carriers** — `StarkSound`
   (`CircuitSoundness.lean:382`), `Poseidon2SpongeCR`
   (`Poseidon2Binding.lean:169`), `Compress8CR` (`DeployedCapTree.lean:630`): the
   FRI/STARK-soundness and Poseidon2-CR floor, carried as classes/Prop
   hypotheses. Zero raw `axiom` declarations in `Dregg2/Circuit/`.
