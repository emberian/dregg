# VK as Re-Execution Recipe

**Date:** 2026-05-24
**Lane:** Silver Vision substrate honesty
**Status:** design landed; canonical encoders implemented; starbridge-apps migrated to canonical VKs.

## §1. Thesis

> Until plonky3 recursion lands, every `vk_hash`, `child_program_vk`, and
> `WitnessedPredicateKind::Custom { vk_hash }` in pyana commits to a
> **canonical encoding of executable bytes** that any validator can
> re-execute against witness data to verify the executor's claim.

A VK in pyana, today, is not the verifying key of a recursive SNARK. It is
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

Pyana has three places where a `[u8; 32]` VK identifier names an
executable artifact. Each gets a canonical encoding.

### §2.1. `FactoryDescriptor.child_program_vk`

The child VK names a `CellProgram` — the executable state-transition
governor installed on cells produced by the factory.

**Canonical bytes:**

```
H_program_vk = BLAKE3_keyed("pyana-cellprogram-vk-v1", postcard(CellProgram))
```

- `postcard` is already pyana's canonical serialization for cell-side
  types (used by `FactoryDescriptor::hash`, `Cell::seal`, etc.); it is
  deterministic given `Serialize` implementations are.
- BLAKE3 keyed-derive with the domain string `"pyana-cellprogram-vk-v1"`
  prevents cross-domain collisions with other `[u8; 32]` hashes
  (factory descriptor hashes, child-vk derivation hashes, …).
- `v1` in the domain string is the encoding-format version. A future
  change to `CellProgram`'s shape that breaks postcard determinism
  bumps to `v2`.

The encoder is `pyana_cell::factory::canonical_program_vk(&CellProgram) -> [u8; 32]`.

### §2.2. `WitnessedPredicateKind::Custom { vk_hash }`

The custom kind names an app-defined predicate algebra. The canonical
encoding is parameterized by the predicate's authoring representation
(currently DSL bytes; future: WASM bytecode, AIR descriptor, Pickles
circuit serialization). v1 commits the *opaque bytes* the app author
provides:

```
H_predicate_vk = BLAKE3_keyed("pyana-witnessed-predicate-vk-v1", canonical_bytes)
```

The encoder is `pyana_cell::predicate::canonical_predicate_vk(&[u8]) -> [u8; 32]`.

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
  needs the registry replicated. Pyana already replicates federation
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
**degrades to self-contained** when network conditions demand. Pyana
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
H_program_vk = BLAKE3_keyed("pyana-pickles-circuit-v1", pickles_serialization(circuit))
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

1. `pyana_cell::factory::canonical_program_vk(&CellProgram) -> [u8; 32]`
   — postcard + BLAKE3_keyed.
2. `pyana_cell::predicate::canonical_predicate_vk(&[u8]) -> [u8; 32]`
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
