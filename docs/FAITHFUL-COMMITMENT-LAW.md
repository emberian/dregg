# The Faithful-Commitment Law

**Every 32-byte component that flows into the deployed state commitment binds its
SOURCE at the system's own soundness strength (~124-bit, the 8-felt encoding) —
never a lossy 1-felt projection.**

## Why this is a law, not a preference

The deployed state commitment once carried components folded **32 bytes → ONE
BabyBear** (`fold_bytes32_to_bb`, a Horner fold). A single BabyBear is ~31 bits,
so two distinct 32-byte values collide with probability ~`1/p ≈ 2^-31`. That is
**far below** the system's own ~130-bit FRI/STARK soundness floor: an adversary
who can grind a 31-bit collision can show a light client a forged committed state
that the proof still accepts.

The insidious part: **a bare `BabyBear` limb carries no evidence of
faithful-vs-degraded.** A faithful 8-felt binding and a degraded 1-felt fold are
the same type (`BabyBear` / `[BabyBear; …]`), so a lossy fold slid into the
commitment silently and was only found by a **bit-audit months later** — then
cost weeks to grind back to faithful 8-felt. The cost of catching it at write
time is one CI second; the cost of not catching it is the months-to-weeks loop.

See the historical analysis in `.docs-history-noclaude/FAITHFUL-STATE-COMMITMENT.md`
and the memory note *Don't Launder a Load-Bearing Insecurity*.

## The rule

- **Degraded (forbidden in a commitment position):** `fold_bytes32_to_bb(x)` —
  32 bytes → 1 felt (~31-bit). Defined in `circuit/src/effect_vm/helpers.rs`.
- **Faithful (required):** `bytes32_to_8_limbs(x)` → `[BabyBear; 8]` (~124-bit),
  and its hash-domain siblings (`hash_many` over 8-felt groups). The commit binds
  the **source**, not a degraded projection of it.

A degraded fold is a fine **consistency tag** where the *real* binding lives
elsewhere (defense-in-depth), and a fine per-effect param projector. It is a
**bug** only when it IS the commitment of a 32-byte component.

## Where the law bites (the commitment-bearing producers)

| File | Role |
|------|------|
| `cell/src/commitment.rs` (`compute_rotated_pre_limbs`) | the canonical `pre_limbs` the rotation commits |
| `turn/src/rotation_witness.rs` | the producer twin of the above |
| `circuit/src/effect_vm/trace_rotated.rs` | the rotated trace that re-absorbs `pre_limbs` |

Non-commitment uses of the fold are **out of scope and sound**: the executor/SDK
per-effect param projectors (`effect_vm_bridge.rs`, `cipherclerk.rs`), the D5 PI
cross-binding reconstruction (`proof_verify.rs`, `node/src/turn_proving.rs` — the
real binding is the `SCHEMA_NOTE_SPEND` proof + the committed set), and tests.

## The gate

`scripts/check-no-degraded-felt.sh` runs `ast-grep` against the producers above
(rule `.ast-grep/rules/faithful-commitment-felt.yml`, scoped by its `files:`
field). Wired into CI as the **`no-degraded-felt`** job in `.github/workflows/ci.yml`.
A net-new `fold_bytes32_to_bb` in a commitment producer **fails the PR**.

### Allowlisting a deliberate residual

A justified residual is annotated inline, line-scoped:

```rust
// FAITHFUL-COMMITMENT-LAW residual: <why this is safe / when it gets fixed>.
pre[4 + i] = fold_bytes32_to_bb(&cell.state.fields[i]); // ast-grep-ignore: degraded-felt-commitment
```

⚠ The text after the directive's colon is parsed by ast-grep as a **rule-id
list**, so the suppression must read exactly `// ast-grep-ignore:
degraded-felt-commitment` (the rule id) — the human REASON goes on the line
ABOVE, never after the colon.

### Current allowlisted residuals

**NONE.** The `fields[0..7]` residual is **CLOSED** (v13 fields-octet epoch): the
r3..r10 Horner folds in `compute_rotated_pre_limbs` and its `rotation_witness`
twin are REPLACED by the faithful `Faithful8::from_field_limbs8` 8-lane split
(lane 0 = the u64-lane lo32 riding the welded limb `4 + i`, lanes 1..7 riding the
new completion lanes `112 + 7·i .. +6` — `NUM_PRE_LIMBS` 112→169). The state
commitment now binds ALL 32 bytes of every flat field at ~124 bits. The ast-grep
allowlist directives are gone; the gate PASSES with zero fields entries.

The **one remaining in-circuit seam** (a CIRCUIT weld, NOT a degraded producer
felt): the setField[0..7] WRITTEN slot's 7 completion lanes ride the
deliberately-gated setField **VALUE8 weld** follow-on (forcing them to the declared
value8 params). This is a named circuit residual, not a lossy commitment.

**Deployed reality (2026-07-03 R1 audit, `circuit/tests/setfield_completion_lane_forge.rs`):**
the DEPLOYED registry member (`EffectVmEmitRotationV3.lean:5363`) is
`v3OfFrozen (setFieldTickFace slot)` — freeze-**ALL**, so the written slot's own
completion lanes are FROZEN before==after too (bound to the pre-state). The
`fieldsCompletionFreezesExcept` / `setFieldV3` "except" variant is defined + carries
the value keystones but is NOT deployed. Consequence: a forge of the written field's
high 224 bits is UNSAT (the freeze bites — no ledgerless silent-forge), but an
honest LARGE-value setField (high bytes ≠ pre-state) currently cannot prove. So the
seam is a **completeness** residual (the value8 weld unlocks faithful large-value
writes AND declared-value binding), NOT a soundness hole. VK-affecting; gated.

## The capstone: the `Faithful8` TYPE WALL (built)

The type-level capstone **exists**: `dregg_circuit::faithful8::Faithful8`
(`circuit/src/faithful8.rs`, re-exported as `dregg_circuit::Faithful8`) — a
newtype over `[BabyBear; 8]` with a **private** inner array, so a bare octet
cannot enter a commitment sink without naming a faithful constructor. A
degraded felt in a typed commitment position is now a **compile error**
(`compile_fail` doc-tests in the module are the tripwire).

**Constructors (the only ways in):**

- `Faithful8::from_bytes32` — `bytes32_to_8_limbs`, the canonical 32-byte limb split;
- the **tree roots** — `cap_root::compute_capability_root{,_with_tombstones}`,
  `cap_root::empty_capability_root`, `heap_root::compute_canonical_heap_root_8{,_entries}`,
  `heap_root::empty_heap_root_8`, `CanonicalHeapTree8::root8` all *return* `Faithful8`
  (internally via the crate-private `from_root8`);
- the **wire-commit chain** — `from_wire_commit` / `from_wire_commit_chip`;
- `from_canonical_key` — the 30-bit KEY_COMMIT packing (the `pubkey8` lane);
- `from_field_limbs8` — the v13 **flat-fields[0..7] octet** projection (`field_limbs8`:
  lane 0 = u64-lane lo32, lanes 1..7 = the higher bytes), THE constructor for the
  `fields[0..7]` octets (it REPLACED the `from_lossy_31bit_DANGER` fields hatch);
- `Faithful8::ZERO` — the absent-material / vk-revoke sentinel;
- `Faithful8::from_lossy_31bit_DANGER(reason, limbs)` — the **greppable escape
  hatch** for named residuals (currently UNUSED — the burn-down list is empty).

**Typed sinks:** the octet fills of the three commitment producers
(`cell::commitment::compute_rotated_pre_limbs`, `turn::rotation_witness::produce`,
and the `trace_rotated` accumulator-lane overrides) go through
`Faithful8::write_octet` / `write_lanes`; the cell digest producers
(`compute_authority_digest_8`, `perms_digest_8`, `vk_digest_8`,
`compute_canonical_capability_root_8`, `state::compute_canonical_{heap,fields}_root_8`,
`compute_canonical_state_commitment_v9_felt8`, `rotation_witness::wire_commit_8`)
all return `Faithful8`. Reading out is unrestricted (`Deref` / `.limbs()` /
`Into<[BabyBear; 8]>`) — the wall polices construction, not inspection, which is
what stops the consumer cascade at module boundaries. Circuit-internal trace
math stays bare `BabyBear` by design.

**Gate + wall are complementary:** the ast-grep gate catches the degraded
*pattern* (`fold_bytes32_to_bb` in a producer file, including sites that never
touch a typed sink); the wall catches the degraded *value* (any bare octet
smuggled toward a typed sink, in any file, including ones the gate has never
heard of). Neither subsumes the other; both stay.

### The `_DANGER` sites = the v13 burn-down list — **EMPTY (v13 DONE)**

`grep -rn from_lossy_31bit_DANGER --include='*.rs'` IS the burn-down list. It is
now **empty** of call sites: the `fields[0..7]` residual pair
(`cell/src/commitment.rs::compute_rotated_pre_limbs` +
`turn/src/rotation_witness.rs::produce`) was the last one, closed by the v13
fields-octet grow (`Faithful8::from_field_limbs8`). The constructor is retained
as the greppable hatch for any FUTURE named residual.

Adding a new `_DANGER` site without listing it here is a review-time violation.
