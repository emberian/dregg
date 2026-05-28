# VK as Re-Execution Recipe

**Date:** 2026-05-24
**Lane:** Silver Vision substrate honesty
**Status:** design landed; canonical encoders implemented; starbridge-apps migrated to canonical VKs.

## §1. Thesis

> Until plonky3 recursion lands, every `vk_hash`, `child_program_vk`, and
> `WitnessedPredicateKind::Custom { vk_hash }` in dregg commits to a
> **canonical encoding of executable bytes** that any validator can
> re-execute against witness data to verify the executor's claim.

A VK in dregg, today, is not the verifying key of a recursive SNARK. It is
the cryptographic name of *what the validator is supposed to run*. When a
factory says "I create cells with program VK `H`", an honest peer should be
able to recover the program text whose canonical hash is `H`, run that
program against the cell's transition stream, and confirm acceptance.

This is the **Silver Vision** stance: substrate honesty pre-recursion.
The recipe is bloated relative to a real recursive proof (a few hundred
bytes for a typical `CellProgram` vs. a few kilobytes for a real STARK
verifier key — and zero validator-side re-execution work for the
recursive case), but it is *algebraically sound* — there is nothing the
executor can claim about a VK that a validator with the canonical bytes
cannot independently verify.

This document is the contract for that recipe: what bytes go in, what
hash comes out, where the bytes live, and how the transition to real
recursive VKs preserves the `vk_hash` identifier.

## §2. Canonical encodings (per VK kind)

`dregg` has three places where a `[u8; 32]` VK identifier names an
executable artifact. Each gets a canonical encoding.

### §2.1. `FactoryDescriptor.child_program_vk`

The child VK names a `CellProgram` — the executable state-transition
governor installed on cells produced by the factory.

**Canonical bytes:**

```
H_program_vk = BLAKE3_keyed("dregg-cellprogram-vk-v1", postcard(CellProgram))
```

- `postcard` is already dregg's canonical serialization for cell-side
  types (used by `FactoryDescriptor::hash`, `Cell::seal`, etc.); it is
  deterministic given `Serialize` implementations are.
- BLAKE3 keyed-derive with the domain string `"dregg-cellprogram-vk-v1"`
  prevents cross-domain collisions with other `[u8; 32]` hashes
  (factory descriptor hashes, child-vk derivation hashes, …).
- `v1` in the domain string is the encoding-format version. A future
  change to `CellProgram`'s shape that breaks postcard determinism
  bumps to `v2`.

The encoder is `dregg_cell::factory::canonical_program_vk(&CellProgram) -> [u8; 32]`.

### §2.2. `WitnessedPredicateKind::Custom { vk_hash }`

The custom kind names an app-defined predicate algebra. The canonical
encoding is parameterized by the predicate's authoring representation
(currently DSL bytes; future: WASM bytecode, AIR descriptor, Pickles
circuit serialization). v1 commits the *opaque bytes* the app author
provides:

```
H_predicate_vk = BLAKE3_keyed("dregg-witnessed-predicate-vk-v1", canonical_bytes)
```

The encoder is `dregg_cell::predicate::canonical_predicate_vk(&[u8]) -> [u8; 32]`.

Apps that author DSL predicates pass `postcard(dsl_ast)`. Apps that
author WASM pass the WASM bytecode. The choice of authoring representation
is documented per-app; the VK commits to *the same bytes the validator
will use to re-execute*.

Note: `WitnessedPredicate::commitment` continues to bind audience /
shape (route-table root, fact commitment, set commitment, etc.) as
distinct from `vk_hash`. The vk_hash names the *verifier*; the
commitment names the *instance*.

### §2.3. `Authorization::Custom { predicate: WitnessedPredicate { kind: Custom { vk_hash }, .. } }`

Carries through to §2.2 — the `vk_hash` inside the authorization's
predicate is the same canonical predicate VK. No separate encoding.

This is the design pivot that makes `Authorization::Custom` honest
pre-recursion: a verifying node receives the authorization, looks up
the canonical predicate bytes (§4), re-executes them against the
action's `witness_blobs[proof_witness_index]` resolved input, and
accepts iff the predicate accepts. Until recursion lands, the
"acceptance-inside" boundary for `Authorization::Custom` is not a
STARK verifier — it is *the validator re-running the program*.

### §2.4. `Effect::Custom { vk_hash }`

The existing `Effect::Custom` variant uses the same encoding as §2.2.
The vk_hash inside it points at an AIR / verifier specification whose
canonical bytes are stored in the program registry.

## §3. Re-execution protocol

Given:
- A VK identifier `vk_hash: [u8; 32]`
- Witness data (action's `witness_blobs`, cell's old/new state,
  context fields)
- Claimed acceptance bit from the executor's receipt

Any validator:

1. **Recovers the canonical bytes** keyed on `vk_hash` from the
   program registry (§4). If the registry has no entry, the validator
   *cannot verify* and must either request the bytes from the executor
   (extending the receipt with a self-contained witness blob) or
   reject.
2. **Verifies the binding:** `BLAKE3_keyed(domain, bytes) == vk_hash`.
   A mismatch is a fatal protocol error (the registry returned wrong
   bytes; investigate registry corruption or executor lying).
3. **Decodes** the canonical bytes into the live type (`CellProgram`
   from postcard for §2.1; opaque predicate input for §2.2 — each
   predicate authoring representation has its own deserializer).
4. **Resolves the input** per `WitnessedPredicate.input_ref`
   (cleartext-inside the validator: it sees the slot/witness/sender
   values that go into the predicate).
5. **Re-executes** the program/predicate against the resolved input
   + witness data. For `CellProgram`, this is `program.evaluate_full(
   new_state, old_state, ctx, meta, &witnesses)` — the same code path
   the executor used. For custom predicates, the deserialized
   verifier reads the proof bytes and accepts/rejects.
6. **Compares acceptance bit:** validator's bit must equal the
   receipt's claimed bit. Disagreement is a soundness failure —
   the executor lied or the witness data was tampered with.

The whole protocol is deterministic given the canonical bytes and the
witness data. No randomness, no time-of-validation state — the receipt
+ canonical bytes + witness data are fully sufficient.

### §3.1. What a validator learns

Per `BOUNDARIES.md §5.1`:

- **Cleartext-inside the VK author:** they wrote the program text; they
  see everything.
- **Cleartext-inside the validator (re-execution venue):** they see the
  program text (from the registry) AND the witness data. This is
  *the* boundary cost of the recipe — pre-recursion, the validator
  population is cleartext-inside.
- **Commitment-inside the receipt observer:** they see only `vk_hash` +
  the acceptance bit. They do not see the program text unless they
  pull it from the registry.
- **Acceptance-inside the on-chain consensus:** consensus sees the
  receipt's acceptance bit plus the validator quorum's agreement on
  it.
- **Out-of-band everyone else.**

Post-recursion (§7), the validator population narrows to
*acceptance-inside* — it sees a small proof, not the program text.

## §4. Bloat tradeoff

A `CellProgram::Cases` with ~5 transition cases and ~30 total constraints
postcard-encodes to roughly 400–800 bytes. The five-case subscription
program: ~640 bytes. The nameservice three-constraint program: ~50
bytes. The identity issuer program: ~200 bytes.

These are stored once per factory in the registry (a thousand factories
≈ 1 MB of registry state). Receipts that carry inline bytes (§6 Option
B) grow by the size of the program — a few hundred bytes per turn.

The bloat is **acceptable** for Silver Vision: state durably stored is
cheap; per-turn bytes-on-wire are also cheap relative to the witness
blobs already carried. The win is *honesty*: no validator has to take
the executor's word for what the VK means.

For context, a real plonky3 recursive proof of an Effect-VM AIR trace
is ~10-50 KB (depending on column count + FRI parameters). The
canonical recipe is *smaller* than a real proof — bloat is not the
concern. The concern is per-turn re-execution cost, which is bounded
by the cost of running the cell program once (microseconds per
constraint).

## §5. Migration to recursion

When plonky3 recursion lands (Golden-Edge Block 2+), every canonical
recipe gets a recursive-proof counterpart:

```
H_program_vk_v1 == BLAKE3(canonical_bytes)       // unchanged
H_program_vk_v2 == verifying_key(recursive_air(canonical_bytes))
                ?= same hash, different artifact behind it
```

The `vk_hash` identifier in `FactoryDescriptor`,
`WitnessedPredicateKind::Custom`, and `Authorization::Custom`
**stays stable** — apps that pinned `child_program_vk =
canonical_program_vk(&program)` keep that value. What changes is
*the artifact the registry returns when keyed on that hash*: instead
of canonical bytes, it returns a verifying key for a recursive STARK
that attests "I ran the program canonical_bytes against the witness
and accepted." The validator runs a small recursive verifier instead
of re-executing.

Concretely:

1. Add a `RegistryArtifact` enum with two variants:
   - `Canonical { bytes: Vec<u8> }` — current path; validator
     re-executes.
   - `Recursive { verifying_key_bytes: Vec<u8> }` — future path;
     validator runs the recursive verifier.
2. The on-disk hash key is still `vk_hash`. The artifact pointed-to
   evolves.
3. Apps may opt to ship *both* (canonical for backwards-compatible
   audit + recursive for fast verification). Receipts indicate which
   path they used; validators may request the other on dispute.

This is the **transparent compression**: the protocol identifier
stays; the underlying artifact gets denser. No app code changes; no
factory descriptor changes; only the registry and verifier code path.

## §6. Registry vs. inline (where bytes live)

The canonical bytes have to live somewhere. Two options, both
algebraically equivalent (the same `vk_hash` discipline):

### §6.1. Option A — separate program registry

A `ProgramRegistry` cell (or sealed-storage map) holds
`(vk_hash, canonical_bytes)` entries. VK consumers (factories,
authorizations, effects) reference by hash; bytes live once.

- **Pro:** compact wire/receipt footprint (a turn references the VK,
  not the bytes).
- **Pro:** apps that publish multiple factories sharing a child
  program get bytes deduplicated.
- **Pro:** the registry's own state is a cell with a `CellProgram`
  enforcing `WriteOnce`-by-hash semantics — anyone can audit "the
  registry has not been tampered with."
- **Con:** validators must pull from the registry; offline validation
  needs the registry replicated. `dregg` already replicates federation
  state, so this is no worse than existing reach.

### §6.2. Option B — inline bytes on receipts

Each `WitnessedReceipt` scope-2 witness blob carries the canonical
bytes of every VK referenced by the turn.

- **Pro:** self-contained — a receipt is verifiable in isolation, no
  registry pull.
- **Con:** receipts grow by the size of every program touched. A
  high-throughput cell whose program is 2 KB and that produces 1000
  receipts/day costs 2 MB/day of receipt-only bytes.
- **Con:** byte duplication on every turn for the same program.

### §6.3. Recommendation

**Option A for the steady state; Option B for the dispute path.**

Steady state: factories register canonical bytes in
`ProgramRegistry` at deploy time (the existing `FactoryRegistry`
already names factories by hash; it gets an extra `program_bytes` slot
or an adjacent `ProgramRegistry`). Receipts reference by `vk_hash`.

Dispute path: when a validator cannot fetch from the registry (offline,
adversarial federation, etc.) it asks the executor to supply the bytes
inline. The receipt's existing `WitnessBundle` shape (`turn::WitnessBlob`)
admits a `Cleartext` kind that holds the canonical bytes;
the validator computes `BLAKE3_keyed` and rejects mismatches.

This **defaults to compact** (compute-cheap, bytes-cheap) and
**degrades to self-contained** when network conditions demand. `dregg`
already has both layers wired (registries + witness blobs); the
program registry is one more registry of the same shape.

For *this* lane (Phase 2), neither registry storage nor inline witness
carriage is implemented — what lands is the encoder and the
starbridge-apps switching their VK constants from byte-string
placeholders (`*b"starbridge-nameservice-childprog"`) to
`canonical_program_vk(&program)`. The registry surface is left for the
follow-on lane that wires Option A into `FactoryRegistry`.

## §7. Pickles compatibility (and the recursion landscape)

Per `KIMCHI-SURVEY.md` Option B, Mina's Pickles is a candidate outer
layer. If Pickles becomes the outer recursion, the canonical encoding
generalizes:

```
H_program_vk = BLAKE3_keyed("dregg-pickles-circuit-v1", pickles_serialization(circuit))
```

The same `vk_hash` discipline holds: the hash names a canonical
representation of *the verifier circuit Pickles will check*. Validators
either re-execute the Pickles circuit (acting as Pickles wrapper)
or accept the Pickles proof itself.

The substrate is encoding-agnostic — `canonical_program_vk` and
`canonical_predicate_vk` are domain-keyed BLAKE3 hashes of *whatever
canonical-bytes representation* the app chose. v1 picks
postcard(CellProgram) and opaque-bytes(predicate) as the bootstrap;
v2/v3 can pick richer representations under domain strings
`-vk-v2` / `-vk-v3` without breaking the identifier shape.

## §8. Boundary contracts (per BOUNDARIES.md §5.2)

For VK as re-execution recipe pre-recursion:

```
/// Boundary contract:
/// - Cleartext-inside:  VK author (writes the program), validators
///                      (pull canonical bytes from registry / receipt
///                      to re-execute).
/// - Commitment-inside: receipt observers (see vk_hash + acceptance bit);
///                      consensus nodes that don't validate VK semantics.
/// - Acceptance-inside: validators (learn only accept/reject; the
///                      bytes go into the head, the result comes out).
///                      Note: pre-recursion they are also cleartext-inside.
/// - Out-of-band:       everyone outside the validator + observer
///                      populations.
/// Enforced by: BLAKE3_keyed binding canonical bytes to vk_hash.
/// Failure mode if violated: validator computes a different acceptance
/// bit than the executor — soundness failure, escalate to consensus.
```

Post-recursion, **cleartext-inside collapses to "VK author only"** —
validators see only the recursive verifying key and the proof, not
the program text.

## §9. Implementation summary (Phase 2)

What lands this lane:

1. `dregg_cell::factory::canonical_program_vk(&CellProgram) -> [u8; 32]`
   — postcard + BLAKE3_keyed.
2. `dregg_cell::predicate::canonical_predicate_vk(&[u8]) -> [u8; 32]`
   — opaque bytes + BLAKE3_keyed.
3. `FactoryDescriptor::validate_child_vk_canonical(&CellProgram) ->
   Result<(), FactoryError>` — checks that `self.child_program_vk ==
   Some(canonical_program_vk(program))`. Lets a validator with both
   the descriptor and the program text confirm the binding without
   trusting the executor.
4. Tests covering: determinism, sensitivity to program content,
   sensitivity to predicate bytes, mismatch rejection.
5. `starbridge-apps`:
   - `nameservice`: adds `name_cell_program()` returning the
     `CellProgram::always(state_constraints)` carrying
     `WriteOnce(NAME_HASH)`, `Monotonic(EXPIRY)`,
     `WriteOnce(REVOKED)`. The `NAME_CHILD_PROGRAM_VK` constant
     becomes `canonical_program_vk(&name_cell_program())`.
   - `identity`: adds `issuer_program()` returning the
     `CellProgram::always(state_constraints)` carrying the four
     issuer caveats. `ISSUER_CHILD_PROGRAM_VK` becomes
     `canonical_program_vk(&issuer_program())`.
   - `subscription`: already has `subscription_program()`.
     `SUBSCRIPTION_CHILD_PROGRAM_VK` becomes
     `canonical_program_vk(&subscription_program())`.

What this *closes:* the substrate-honesty gap that
`NAME_CHILD_PROGRAM_VK = *b"starbridge-nameservice-childprg"` (and the
two siblings) created. A validator with the VK constant + the
canonical program function can verify the constant binds to the
program text. Pre-this-change, it was a stable placeholder unconnected
to anything executable.

What this *leaves open* (deliberate, follow-on lanes):

- `ProgramRegistry` storage path (Option A from §6).
- Inline canonical bytes on receipts (Option B from §6).
- `WitnessedPredicateKind::Custom` callers in the tree (none today,
  but the encoder is in place when apps want it).
- `Effect::Custom` migration (no current consumers; same encoder
  applies).
- Recursion (§5) — a separate Golden-Edge block, not this lane.

## §10. Cross-references

- `NEW-WORLD.md` — Silver Vision context.
- `AUTHORIZATION-CUSTOM-DESIGN.md` — `Authorization::Custom`'s
  `vk_hash` flow.
- `PREDICATE-INVENTORY.md` — `WitnessedPredicateKind::Custom` shape.
- `KIMCHI-SURVEY.md` — recursion landscape including Pickles
  generalization (§7).
- `BOUNDARIES.md` §5.2 — the boundary contract vocabulary used in §8.
- `STAGE-7-GAMMA-2-PI-DESIGN.md` — γ.2's PI exposure model; recipe-VKs
  do not interact with γ.2 directly (γ.2 binds *across* cells; VK
  binds *within* a cell's program).
- `EXECUTOR-HONESTY-AUDIT.md` — this lane is broadly a T13 substrate
  ("executor claims a VK"): pre-recursion, the recipe makes the
  claim falsifiable by re-execution.

## §v2. Layered VK structure (supersedes §2.1–§2.4 for new code)

### §v2.1. The soundness gap v1 left open

v1 (§2.1–§2.4 above) committed `vk_hash` to a single thing: the
canonical byte serialization of the program / predicate / effect
spec. That commits to *what the validator is supposed to run* — but
not to *which AIR runs it*, *which verifier-impl adjudicates the
trace*, or *which proving system produces the proof*. Two cells with
the same `CellProgram` value but different AIRs (say, the Effect VM
AIR vs. a hypothetical Effect VM v2 AIR with extra constraint rows
and a different PI layout) **share** a vk_hash under v1. Validators
cannot tell them apart from the VK alone, which is the wrong story:
the executor's claim "I proved acceptance under VK `H`" is
satisfiable by either AIR if the program text is the same.

v2 closes this gap by binding `vk_hash` to **four** components, not
one.

### §v2.2. The four-component encoding

```rust
pub struct VkComponents<'a> {
    pub program_bytes: &'a [u8],        // canonical postcard(CellProgram), DSL AST, opaque bytes
    pub air_fingerprint: [u8; 32],      // hash of the AirDescriptor
    pub verifier_fingerprint: [u8; 32], // SourceHash / WasmHash / CompiledVkHash
    pub proving_system_id: ProvingSystemId,
}

pub fn canonical_vk_v2(c: &VkComponents) -> [u8; 32] {
    BLAKE3_keyed("dregg-vk-v2",
        len(c.program_bytes) || c.program_bytes ||
        c.air_fingerprint ||
        c.verifier_fingerprint.canonical_bytes() ||
        len(ps_bytes) || ps_bytes)
}
```

Each component answers a question the executor's "I ran VK `H`" claim
implicitly depends on:

1. **`program_bytes`** — *what bytes do I run?* The v1 encoding,
   unchanged. The canonical re-execution recipe.
2. **`air_fingerprint`** — *under which AIR's algebra do those bytes
   prove acceptance?* Hash of an [`AirDescriptor`](#airdescriptor)
   capturing the AIR's column count, PI layout, constraint counts,
   max degree. Distinct AIRs ⇒ distinct fingerprints, even when
   shapes coincidentally agree on column count.
3. **`verifier_fingerprint`** — *what code adjudicates the AIR trace?*
   Either a source-hash (in-tree Rust verifier), a wasm-hash (ahead-
   of-time compiled verifier), or a compiled-VK hash (proving-system
   VK blob).
4. **`proving_system_id`** — *which proving system?* Plonky3-BabyBear-
   FRI (pinned to a specific p3 git rev), Kimchi-Pasta, SP1, or a
   custom system. A proof produced by one system is not interchangeable
   with a proof from another even when AIR + program match.

### §v2.3. AirDescriptor

Each hand-written AIR module exports `pub const AIR_DESCRIPTOR:
AirDescriptor` capturing its shape:

```rust
pub struct AirDescriptor {
    pub air_id: &'static str,                  // e.g. "effect_vm_air_v1"
    pub column_count: usize,
    pub public_input_layout: &'static [PiSlot], // {name, offset, length_in_felts}
    pub constraint_polynomial_count: usize,
    pub boundary_constraint_count: usize,
    pub max_degree: usize,
    pub source_hash: Option<[u8; 32]>,         // optional git-blob-hash of the AIR src
}
```

`dregg_circuit::air_descriptor::fingerprint(&d)` BLAKE3-keyed-derives
`"dregg-air-fingerprint-v1"` over the descriptor's fields, with
length-prefixed encoding so concatenation attacks cannot collide two
distinct descriptors.

The three in-tree hand-written AIRs that ship with VK v2 are:

| AIR module           | `air_id`                 | column_count       | PI slots       |
|----------------------|--------------------------|--------------------|----------------|
| `effect_vm`          | `effect_vm_air_v1`       | `EFFECT_VM_WIDTH`  | 41 slots covering commitments, balances, bilateral roots, sovereign-witness teeth, value limbs |
| `note_spending_air`  | `note_spending_air_v1`   | `NOTE_SPENDING_WIDTH` (19) | 5 slots: nullifier, merkle_root, value, asset_type, destination_federation |
| `bridge_action_air`  | `bridge_action_air_v1`   | `BRIDGE_ACTION_WIDTH` (26) | 5 slots: nullifier (8), recipient (8), destination_federation (8), amount_lo, amount_hi |

Future AIRs follow the same pattern: a `pub const AIR_DESCRIPTOR` at
the bottom of the module, named `<name>_air_v<n>`.

### §v2.4. ProvingSystemId

```rust
pub enum ProvingSystemId {
    Plonky3BabyBearFri { p3_rev: &'static str },  // current default
    KimchiPasta,
    Sp1V6,
    Custom { id: &'static str },
}
```

For dregg today, cell-program VKs all use `Plonky3BabyBearFri { p3_rev: PLONKY3_PINNED_REV }`
where `PLONKY3_PINNED_REV` is the workspace's plonky3 git rev. A
plonky3 bump that changes the rev cascades into every cell-program
vk_hash — by design.

### §v2.5. VerifierFingerprint

```rust
pub enum VerifierFingerprint {
    SourceHash([u8; 32]),     // git-blob-hash of the verifier's Rust source
    WasmHash([u8; 32]),       // BLAKE3 of wasm-compiled verifier bytes
    CompiledVkHash([u8; 32]), // hash of proving-system VK bytes
}
```

For the three in-tree hand-written AIRs, the v2 lane initially uses
`SourceHash(keyed_derive("dregg-effect-vm-verifier-v1", AIR_DESCRIPTOR.air_id))`
as a sentinel — pinned to the AIR identifier rather than the literal
source file hash. A follow-on lane wires `git hash-object` into the
build so the fingerprint binds to the live source-tree state.

### §v2.6. Consumer surface

- **`dregg_cell::factory::canonical_program_vk_v2(program, air_fp,
  verifier_fp, proving_system)`** — the v2 cell-program VK encoder.
  Layered hash; commits to all four components.
- **`dregg_cell::predicate::canonical_predicate_vk_v2(bytes, ...)`** —
  the v2 custom-predicate VK encoder.
- **`dregg_cell::CustomEffectRegistry::register(canonical_bytes,
  air_fp, verifier_fp, proving_system, verifier)`** — registration
  upgraded to validate the layered hash. Returns
  `CustomEffectError::LayeredBindingMismatch` when the verifier's
  claimed vk_hash does not match the v2 hash of the components.
- **`dregg_app_framework::canonical_program_vk(program)`** — the
  user-facing entry point for app authors. Hides the four-tuple
  behind the same one-argument shape v1 used; fills in Effect VM AIR
  fingerprint, sentinel verifier fingerprint, and Plonky3 proving
  system. Starbridge-apps' `*_child_program_vk()` functions pick up
  v2 hashes automatically through this wrapper.
- **`dregg_app_framework::validate_child_vk_canonical(descriptor,
  program)`** — v2 validation wrapper; calls
  `FactoryDescriptor::validate_child_vk_canonical_v2` with the same
  four components.

The legacy `dregg_cell::canonical_program_vk(program)` (v1, program-
bytes only) remains as a building block exposed under the explicit
name `dregg_app_framework::canonical_program_bytes_hash` for callers
that want the unlayered hash (e.g., to print both v1 and v2 in an
inspector during migration).

### §v2.7. Migration v1 → v2

**Greenfield. No backcompat path.** All callers move to v2 in one
sweep:

- vk_hash constants in the tree change. The numerical value of
  every starbridge-app's `*_child_program_vk()` is now the v2 hash;
  the v1 hash is no longer used anywhere in the production path.
- Receivers (factory registries, custom-predicate registries,
  custom-effect registries) accept the new hashes uniformly.
- v1 and v2 *never* collide — domain separation under
  `"dregg-vk-v2"` (vs. `"dregg-cellprogram-vk-v1"` and
  `"dregg-witnessed-predicate-vk-v1"`) guarantees disjoint hash
  spaces. A v1 hash and a v2 hash for the same program are
  guaranteed-different values.
- Receipts and consensus state that pinned v1 hashes need to be
  regenerated. (For dregg today this is acceptable — there is no
  long-lived consensus state pinning the old VK constants outside
  test fixtures; greenfield migration discards the v1 values.)

### §v2.8. Boundary contract (per BOUNDARIES.md §5.2)

```
/// Boundary contract (VK v2):
/// - Cleartext-inside:  VK author (knows all four components) +
///                      validators (re-execute the program bytes
///                      against the AIR + verifier identified by the
///                      remaining three components).
/// - Commitment-inside: receipt observers (see vk_hash_v2 + acceptance
///                      bit only).
/// - Acceptance-inside: post-recursion validators (proof + verifying
///                      key; do not need the program bytes).
/// - Out-of-band:       everyone else.
/// Enforced by: BLAKE3 keyed-hash domain separation under "dregg-vk-v2",
///   length-prefixed encoding around variable-length components.
/// Failure mode if violated: validator computes a vk_hash that does
///   not match the executor's claim → reject; soundness signal, not
///   soundness loss.
```

### §v2.9. Why not in v1?

The v1 design assumed a single AIR per program type (the Effect VM
AIR for cell programs; the DFA AIR for DFA predicates; etc.) and a
single proving system (Plonky3 STARK with BabyBear+FRI). Both
assumptions held in early development. Once apps started defining
custom predicates with their own AIRs (and the proving-system
roadmap added Kimchi-Pasta for Mina interop and SP1 for off-tree
recursion), the single-AIR / single-system assumption broke and the
v1 hash became insufficient. v2 makes the four-component identity
explicit so future apps can declare their own AIR + proving-system
combos without colliding with existing identifiers.
