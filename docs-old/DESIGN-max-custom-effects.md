# DESIGN: `MAX_CUSTOM_EFFECTS` — constraints, costs, and per-cell-program design

Status: design proposal
Scope: `circuit/src/effect_vm.rs`, `turn/src/executor.rs`, cell-state widening (Stage 1 of `EFFECT-VM-SHAPE-A.md`)

---

## 1. What does `MAX_CUSTOM_EFFECTS` actually constrain?

The constant is declared at `circuit/src/effect_vm.rs:396`:

```rust
pub const MAX_CUSTOM_EFFECTS: usize = 4;
pub const CUSTOM_ENTRY_SIZE: usize = 8;   // 4 vk_hash + 4 proof_commit
pub const CUSTOM_PROOFS_BASE: usize = 11; // BASE_COUNT
```

The PI layout (`pi` module, `effect_vm.rs:358-399`) reserves space *per declared custom effect*, not for a fixed number of slots:

```
PI[0..11]   = base inputs (commits, net_delta, effects_hash, count, balance limbs)
PI[11..]    = for i in 0..custom_count:
                PI[11 + i*8 .. 11 + i*8 + 4] = program_vk_hash
                PI[11 + i*8 + 4 .. 11 + i*8 + 8] = proof_commitment
```

`PI[CUSTOM_EFFECT_COUNT] = pi[6]` is the *prover-declared* number of custom-effect entries appended after the base region. The PI vector length is variable: `BASE_COUNT + custom_count * CUSTOM_ENTRY_SIZE` (`effect_vm.rs:3200`).

**Witness generation** (`effect_vm.rs:3177-3197`) collects every `Effect::Custom { vk_hash, proof_commit }` from the input effect list and asserts at panic-level:

```rust
assert!(custom_count <= pi::MAX_CUSTOM_EFFECTS, ...);
```

**Verifier** (`turn/src/executor.rs:1080-1108`) recomputes the same vector by re-filtering `Effect::Custom` from the runtime turn and appends `vk_hash || proof_commit` per effect. PI matching at `turn/src/executor.rs:1117-1164` then enforces, byte-for-byte, that the reconstructed vector equals what the proof exposes (for the default `EffectVmAir` path; custom-program AIRs use their own layout and skip this check).

External-proof verification loops over the PI-declared list at `turn/src/executor.rs:1192-1235`, calling `program.verify_transition` for each `(vk_hash, proof_commit)` extracted from the proof's PI.

**Answer to the three options:**

- (a) **Not** a fixed number of PI slots. PI grows linearly with `custom_count`; unused slots cost zero bytes.
- (b) **Not** a fixed cap on trace rows with `s_custom == 1`. The selector `sel::CUSTOM` (`effect_vm.rs:1111`) is a per-row indicator; the AIR enforces only state-continuity on that row (`effect_vm.rs:1433-1437`). No row count is constrained.
- (c) **Not** a sum-check. There is no AIR constraint `Σ_rows s_custom == PI[CUSTOM_EFFECT_COUNT]`. The constant is enforced only by the witness-gen `assert!`, which a malicious prover can bypass entirely (REVIEW-effect-vm.md:140, item P2-21 at REVIEW-effect-vm.md:85, open question 7 at REVIEW-effect-vm.md:152).

**So `MAX_CUSTOM_EFFECTS` is documentary.** It is a self-imposed witness-generation cap that the AIR neither knows nor enforces. The verifier will happily iterate any number of custom slots that fit in the proof's PI vector.

This matters for §7 (adversarial analysis).

---

## 2. Cost components scaling with `MAX_CUSTOM_EFFECTS`

Take `N` = the per-cell value we eventually pick (currently the workspace constant 4). Costs scale as follows:

| Component | Scaling | Per-slot cost | Notes |
|---|---|---|---|
| Public input vector length | linear | 8 BabyBear elements (~32 bytes serialized) | `pi_len = 11 + N*8` (`effect_vm.rs:3200`). At `N=4`, PI = 43 BabyBears (~172 bytes); at `N=16`, 139 (~556 bytes). |
| Trace width | **constant** | 0 | `EFFECT_VM_WIDTH = 71` (`effect_vm.rs:104`) is fixed; custom effects use the same row layout as other variants. |
| Trace height | unrelated | 0 | Height comes from `EffectVmAir::new(max_effects)` which must be a power of 2 (`effect_vm.rs:992-998`). A custom effect occupies one row like any other. `N` does not change trace height. |
| AIR constraint count | constant | 0 | Constraints are gated by `s_custom`; they are per-row, fixed in number. Adding slots doesn't add gates. |
| Prover work (STARK) | negligible per slot | O(extra PI hashing) | Witness gen just collects entries; PI commitment includes a few more field elements. Dominant cost is trace polynomial commit, which is unchanged. |
| Verifier work (STARK) | negligible per slot | trivial | PI is a Fiat-Shamir absorption; ~one extra hash per 4-8 elements. |
| Verifier work (external proofs) | **linear and dominant** | one full proof verification per slot | `turn/src/executor.rs:1218-1228` calls `program.verify_transition` per slot. For an SP1 / Plonky3 child proof this can be 10-100ms; for Kimchi ~50-200ms. |
| Turn / block payload | linear | ~32 bytes of PI + however large the *child proof* is | The child proofs themselves are carried in `turn.custom_program_proofs` (`turn/src/turn.rs:52,129`), each `proof_bytes` is the dominant cost (typically tens of KB for a recursive STARK, 200-800 bytes for a recursive Halo2/Kimchi). PI is rounding error. |

**Key non-cost.** Unlike a constraint count or column count, this is purely a *quantity* parameter; it does not regenerate the AIR. Changing `N` per cell only changes how many PI slots the verifier processes and how many child-proof verifications it runs.

**Dominant cost is verifier child-proof verification**, not block bloat. If a cell declares `N=16` and emits 16 customs in one turn, the verifier does 16 child verifications regardless of where the constant lives.

---

## 3. Actual upper bounds

- **BabyBear field on PI elements.** None — PI is `Vec<BabyBear>`, no fixed cap in `dregg_circuit`. Each element is ~31 bits (4 bytes serialized canonically).
- **Plonky3 PI handling.** Plonky3 does not impose a PI length limit; PI is folded into the transcript and used in the STARK boundary system. No architectural ceiling within tested ranges (single-digit to a few hundred elements is routine).
- **Network MTU.** `MAX_BLOCKS_PER_PUSH = 100` (`blocklace/src/dissemination.rs:32`) limits gossip batch size in *block count*, not bytes. No per-turn byte cap was found in `turn/`, `wire/`, or `blocklace/`. Network is not a binding constraint at our scale.
- **Cipherclerk effects-per-turn.** No explicit `max_effects_per_turn` constant found in `sdk/`, `intent/`, or `turn/`. The implicit cap is `EffectVmAir::new(max_effects)`, which must be a power of 2 — current code paths construct AIRs with heights up to a few hundred rows.
- **Practical envelope.** A "sane" sovereign cell turn emits 0-3 custom effects: most cells use built-in AIR variants (Transfer, NoteSpend, GrantCapability, …). The pathological cases are domain programs that fan out — a DEX cell might emit (settle, fee, splash, oracle-attestation) = 4. A composite cell that runs a small zk program per slot might want 8-16.

**Practical hard ceiling: 64.** At `N=64`, verifier does 64 sequential child-proof verifications per cell per turn — at 50ms each, that's a 3.2-second verification. Anything beyond that should be a sub-turn or a recursive aggregate proof.

---

## 4. Per-cell-program: what does it mean?

The user wants the cap to come from the cell's program declaration, not from `dregg_circuit`. The natural place:

- Sovereign cells already carry a `SovereignRegistration` with `verification_key_hash` (referenced at `turn/src/executor.rs:1268`).
- `CellProgram` in `circuit/src/dsl/circuit.rs:931` carries program metadata.

**Proposed surface:**

```rust
pub struct CellProgram {
    // existing fields...
    /// Maximum number of `Effect::Custom` slots this program may emit per turn.
    pub max_custom_effects: u8,
}
```

The value lives in the program manifest and is committed-to by `vk_hash` (i.e., it's hashed into the VK so it cannot be retro-edited without producing a different program identity).

**Binding to the AIR.** Two viable shapes:

**Option A: PI-only enforcement.** Keep the AIR PI layout variable-length as today. Verifier reads `cell.program.max_custom_effects` from cell state, then before iterating `extract_custom_proof_commitments`, asserts `custom_count <= cell.program.max_custom_effects`. The AIR itself is unchanged; the limit lives in the executor.

- Pro: zero AIR changes, immediate to implement.
- Con: identical to today's situation — the limit is not part of the algebraic statement. If the executor forgets to check, a malicious prover with control over PI can declare arbitrarily many slots.

**Option B: Slot-mask in the AIR.** Fix the PI layout to always reserve `CAP` slots (e.g., 16). The cell's `max_custom_effects` is included in the cell commitment; the AIR has a boundary constraint that `PI[CUSTOM_EFFECT_COUNT] <= cell.max_custom_effects` (or equivalently, unused slots are zero — a more easily-arithmetized form is `for i in N..CAP: PI[CUSTOM_PROOFS_BASE + i*8 + ..] == 0`).

- Pro: limit is bound to cell identity inside the proof. Sum-check on `s_custom` rows can also be added to close item P2-21 of the review.
- Con: PI is always `BASE_COUNT + CAP*8` regardless of actual use. At `CAP=16`, every proof carries 128 wasted PI elements (~512 bytes) when no custom effects are used.

**Middle ground (recommended).**

Keep PI variable-length (Option A's cheap layout), **add the AIR sum-check** `Σ_rows s_custom == PI[CUSTOM_EFFECT_COUNT]` (fixes P2-21 independently of the per-cell question), and **bind `max_custom_effects` to cell state** so the boundary constraint `PI[CUSTOM_EFFECT_COUNT] <= cell.max_custom_effects` can be evaluated by the verifier from data it already trusts (the old/new commitments include the program identity).

This costs one extra column (or an aux comparison) and one extra PI element, and gives:

- Variable, slot-efficient PI (no padding waste).
- Algebraic binding of count to selector usage.
- Per-cell cap bound to cell identity via `vk_hash`.

---

## 5. Right defaults

| Knob | Recommendation | Rationale |
|---|---|---|
| Default per-cell `max_custom_effects` | **4** | Matches current workspace constant; covers the existing test surface. Most cells will not override. |
| Workspace cap (max value a cell may declare) | **16** | Allows complex sovereign programs (DEX, oracle, multi-step settlement) to emit several customs per turn without recursion. |
| Hard limit (refuse to validate a cell that declares more) | **64** | Bounds worst-case verifier work to ~3s per turn (at 50ms/proof). Beyond this, the program should aggregate child proofs into one. |
| Encoding | `u8` in cell state | One byte; trivial to commit. The 0-64 range fits cleanly with room to grow. |

A cell that doesn't use the custom-effect mechanism at all should declare `max_custom_effects = 0`; the AIR's sum-check then guarantees no `s_custom` row appears, and verifier loop body is dead.

---

## 6. Implementation plan

Aligns with Stage 1 of `EFFECT-VM-SHAPE-A.md:145-170` (commitment widening), which is the natural place to add new committed cell fields.

**Step 1.** Add `max_custom_effects: u8` to `CellProgram` (`circuit/src/dsl/circuit.rs:931`). Include it in the VK hash so the program identity binds to its declared limit. Default 4 for unset / legacy programs.

**Step 2.** Plumb the value to cell state. The cleanest path is to include it in the program-VK side of cell state (already referenced via `verification_key_hash` in `SovereignRegistration`). No new cell-state column needed at the AIR boundary — the AIR reads it indirectly via the program-VK that's already bound.

**Step 3.** AIR sum-check (independent of per-cell work, closes REVIEW item P2-21):

```rust
// Constraint: Σ rows s_custom == PI[CUSTOM_EFFECT_COUNT].
// Implement as an accumulator column: cum_custom column,
// cum_custom[0] = 0, cum_custom[i+1] = cum_custom[i] + s_custom[i],
// boundary: cum_custom[last] == PI[CUSTOM_EFFECT_COUNT].
```

Adds one column (trace width 71 → 72) and one boundary constraint.

**Step 4.** Executor enforcement (`turn/src/executor.rs` around line 1080):

```rust
let cell_max = ledger.get_sovereign_registration(cell_id)
    .and_then(|r| r.max_custom_effects)
    .unwrap_or(MAX_CUSTOM_EFFECTS_DEFAULT); // 4
if custom_count > cell_max as usize {
    return Err(TurnError::CustomEffectLimitExceeded { cell: *cell_id, declared: custom_count, allowed: cell_max });
}
```

This is the cheap check; the AIR's sum-check makes it a defense-in-depth.

**Step 5.** Migration. The first time a sovereign registration is rehydrated post-upgrade, materialize `max_custom_effects = 4`. New registrations supply the value at registration time.

**Step 6.** Remove the workspace constant `pi::MAX_CUSTOM_EFFECTS = 4` — keep the witness-gen `assert!` but driven by the per-cell value passed into `generate_trace_and_pi`.

**Estimated:** 1-2 days, in parallel with Stage 1 of EFFECT-VM-SHAPE-A.

---

## 7. Adversarial analysis

**Threat 1: prover declares more custom effects than its cell's `max_custom_effects`.**

- Today (workspace constant + no AIR check): caught only by the witness-gen `assert!` at `effect_vm.rs:3193`. A malicious prover that writes its own witness generator can simply skip this check and supply a PI with `custom_count = 1000`. Verifier's `extract_custom_proof_commitments` will iterate all 1000 and verify each — DoS, not soundness, *unless* the prover can also forge each child proof's verification.
- Per-cell + executor check (Step 4 above): caught by executor. Still soundness-good. DoS still possible if the executor verifies the STARK before the count check; the order matters — count check first.
- Per-cell + AIR sum-check (Step 3 above): rejected algebraically. The strongest defense; even a malicious executor variant cannot accept it.

**Threat 2: verifier doesn't iterate all declared slots.**

The PI vector is fully exposed in the proof; `extract_custom_proof_commitments` iterates over the declared `custom_count`. As long as that count is itself algebraically bound (Step 3), the verifier cannot under-iterate without producing a mismatch in the PI comparison loop at `turn/src/executor.rs:1126-1163`. Today (no sum-check) the prover can declare `custom_count = 0` while having `s_custom = 1` on some row — the AIR doesn't notice, and the executor will not verify *any* child proof for the "hidden" custom row. **This is a real soundness gap today (REVIEW item P2-21).**

**Threat 3: malicious cell declares `max_custom_effects = 0` and sneaks customs in via `effects_hash`.**

`effects_hash` is computed by `compute_effects_hash` over the full effect sequence (referenced at `turn/src/executor.rs:1075`). If a cell declares `max_custom_effects = 0` but the prover supplies `Effect::Custom { … }` in the input effect list:

- Witness gen places `s_custom = 1` on that row and includes the entry in PI.
- Without sum-check: PI's `custom_count` could be set to 0 while `s_custom = 1` rows exist. `effects_hash` is consistent with the actual rows; PI's count is independent. Verifier iterates 0 custom slots — the custom effect is "invisible".
- With sum-check + per-cell check: `Σ s_custom == PI[CUSTOM_EFFECT_COUNT]` forces count = 1; executor's per-cell check then rejects (`1 > 0`). Safe.

**This is the reason `custom_count` needs an in-AIR sum check, regardless of where `MAX_CUSTOM_EFFECTS` lives.** Moving the limit per-cell does not introduce a new attack but does make the existing soundness gap more dangerous, because the limit is now untrusted cell-supplied data rather than a hardcoded workspace constant. The sum-check is a prerequisite.

**Threat 4: cell with `max_custom_effects = 64` exhausts verifier.**

Bounded by the hard cap. At 64 slots × ~50ms per Plonky3 child = ~3.2s per turn. If a federation has many such cells in a block, throughput collapses. Mitigation: gas/fee model for custom-effect verification, charged proportional to declared cap. Out of scope for this design but worth flagging.

**Threat 5: child proof `proof_commitment` collision.**

Independent of this design — covered as REVIEW item P1-20 (124-bit Blake3-truncated binding). Per-cell does not affect this.

---

## Summary

`MAX_CUSTOM_EFFECTS = 4` is a witness-generation hint, not an algebraic constraint; the AIR enforces nothing and the verifier already accepts variable-length PI. Costs scale linearly only in PI bytes (~32 per slot) and child-proof verifications (~50ms per slot); trace width, trace height, and constraint count are all unaffected.

Move it to a per-cell `max_custom_effects: u8`, committed into the program VK, with a default of 4, a recommended cap of 16, and a hard ceiling of 64. Simultaneously add the AIR sum-check that's been an open review item — without it, the per-cell limit is enforced only by executor convention and a malicious prover can route custom effects past a cell that declared `max_custom_effects = 0`. The sum-check + per-cell value together make the binding algebraic and cell-bound.
