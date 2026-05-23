# CapTP Swiss Number Privacy Analysis

## The Question

Do federation nodes in a hosted-cell deployment learn swiss numbers, and if so, does this break capability security within the federation?

## Architecture Summary

The system has two distinct paths for CapTP effects:

1. **Circuit-level effects** (`circuit/src/effect_vm.rs`): `Effect::ExportSturdyRef` and `Effect::EnlivenRef` are Effect VM opcodes used by SOVEREIGN cells. They exist in the STARK proof trace, not in the plaintext turn.

2. **Executor-level effects** (`turn/src/action.rs`): The `Effect` enum in the turn crate does NOT have ExportSturdyRef or EnlivenRef variants. Hosted cells use the `SwissTable` (`captp/src/sturdy.rs`) directly through the executor.

3. **Swiss number management** (`captp/src/sturdy.rs`): The `SwissTable` is a plain `HashMap<[u8; 32], SwissEntry>` maintained by federation nodes. Swiss numbers are generated with `getrandom`.

## Finding 1: The Threat Model is Different Than Stated

**The stated concern is partially wrong.** Here is why:

### For SOVEREIGN cells (proof-carrying path):

- The `ExportSturdyRef` effect has `random_seed` as a trace column parameter (line 444 of effect_vm.rs)
- `compute_effects_hash()` (line 660) hashes `random_seed` into `effects_hash` (a PUBLIC INPUT at PI[4..5])
- BUT: `effects_hash` is a Poseidon2 hash of ALL effect parameters. The `random_seed` is INSIDE the hash preimage, not exposed directly
- The STARK proof verifier sees `effects_hash` but cannot invert Poseidon2 to recover `random_seed`
- The trace (which contains `random_seed` in cleartext) is the WITNESS -- it is never published

**Conclusion: For sovereign cells, `random_seed` stays private.** The STARK proof hides the witness. Federation nodes see only `(old_commitment, new_commitment, net_delta, effects_hash)`. They cannot derive the swiss number.

### For HOSTED cells (executor path):

- Hosted cells do NOT use the Effect VM at all for ExportSturdyRef
- The `turn/src/executor.rs` `convert_turn_effects_to_vm()` function (line 828-920) maps hosted turn effects to VM effects, but it maps everything that isn't Transfer/SetField/GrantCapability/NoteSpend/NoteCreate to `VmEffect::NoOp`
- The actual `SwissTable` (captp/src/sturdy.rs) is maintained by the federation as server-side state
- Swiss numbers are generated via `getrandom` in `SwissTable::export()` (line 93)
- The SwissTable IS the federation's state -- all nodes that maintain it know all swiss numbers

**Conclusion: For hosted cells, the federation inherently knows all swiss numbers because it IS the vat.** This is not a leak -- it is the fundamental architecture.

## Finding 2: The `effects_hash` Does NOT Leak `random_seed`

The concern was: "effects_hash is a PUBLIC INPUT to the STARK proof... Federation nodes can compute swiss = Hash(cell_id, random_seed, export_counter) from the visible turn."

This is INCORRECT for sovereign cells. Let me trace the exact data flow:

1. `compute_effects_hash()` takes the effect parameters and hashes them with Poseidon2
2. The result `effects_hash` (2 BabyBear field elements) is a PUBLIC INPUT
3. But `effects_hash = Poseidon2(14 || cell_id || permissions || random_seed || export_counter || ...)`
4. Poseidon2 is a collision-resistant hash -- knowing the output does NOT reveal the preimage
5. An observer who sees `effects_hash` cannot determine `random_seed`

**The trace itself** (which contains `random_seed` at row position `PARAM_BASE + param::EXPORT_RANDOM_SEED`) is the ZK witness and is never published. The STARK proof proves statements about the trace without revealing trace values.

## Finding 3: EnlivenRef DOES Expose the Swiss Number in the Effects Hash

For `EnlivenRef`, the situation is different:

```
Effect::EnlivenRef { swiss_number, presenter_id, expected_cell_id, expected_permissions }
```

The `swiss_number` is hashed into `effects_hash`. Same reasoning as above: `effects_hash` is a Poseidon2 hash, so the swiss number is not directly revealed.

BUT: The `EnlivenRef` effect requires the presenter to KNOW the swiss number and present it. The swiss number travels in the Turn data when a sovereign cell enlives a ref. Since sovereign turns carry a STARK proof and only the commitment changes are published, the swiss number stays within the proof witness.

For a HOSTED cell enlivening: the turn IS visible to the federation because the executor must process it. But again -- the executor IS the vat. It needs to look up the swiss number in the SwissTable to grant the capability. This is the fundamental operation.

## Finding 4: The Turn is Published to the Blocklace as Payload

From `blocklace/src/pyana_bridge.rs` (line 166):
```rust
pub fn submit_turn(&self, blocklace: &mut Blocklace, turn_data: Vec<u8>) -> BlockId {
    let block = blocklace.add_block(Payload::Turn(turn_data));
    block.id()
}
```

The serialized turn IS the block payload. For HOSTED cells, this means the full `Turn` struct (with all `Effect`s in the call forest) is visible on the blocklace.

**However**: The hosted cell `Effect` enum (`turn/src/action.rs`) does NOT contain ExportSturdyRef or EnlivenRef. The SwissTable is maintained as EXECUTOR STATE, not as an effect in the turn. Swiss numbers never appear in the turn's serialized form.

## Finding 5: The Actual Exposure Point

The SwissTable (`captp/src/sturdy.rs`) is executor state that all federation nodes maintain as part of their replicated state machine. The question is: do ALL nodes maintain this table, or only a designated subset?

Looking at the architecture:
- The blocklace is fully replicated (all nodes see all blocks)
- Turn execution is replicated (all nodes execute all turns for hosted cells)
- The SwissTable mutations happen AS A SIDE EFFECT of turn execution
- Therefore: all federation nodes have identical SwissTable state

**This means**: Every node in the federation knows every swiss number for every hosted cell. A Byzantine node can use any swiss number to forge capability access.

## Answers to the Specific Questions

### 1. By Design or Bug?

**By design.** In the Goblins model, the vat (a single process) maintains the SwissTable internally. In pyana, the federation IS the vat. All N nodes replicate vat state, including the SwissTable. This is architecturally identical to the single-process case -- the "trust boundary" is the federation boundary, not individual nodes.

The SwissTable is not a "leaked secret" -- it is vat-internal state that happens to be replicated across N processes instead of one.

### 2. Threat Model

- **All N nodes honest**: Equivalent to single-process vat. Swiss numbers are never leaked.
- **One Byzantine node**: That node can access any capability for cells hosted on its federation. BUT: a Byzantine node in a replicated state machine can ALREADY do anything the state machine can do. It already executes all turns. It already sees all state. The swiss number gives it nothing extra -- it could already forge any turn the federation would accept.
- **External adversary (no node access)**: Cannot derive swiss numbers from the blocklace. The Turn data does not contain swiss numbers (they are generated server-side). The effects_hash is opaque.

**Key insight**: A Byzantine node in the hosting federation is equivalent to a compromised vat in Goblins. This is not a capability system vulnerability -- it is the fundamental trust assumption. You trust your hosting federation as you would trust your vat.

### 3. Sovereign Cells

**Confirmed: sovereign cells are secure.** For sovereign cells:
- Swiss numbers are derived inside the STARK proof (Effect VM trace)
- Only the `effects_hash` (Poseidon2 of all effect params) is published
- The `random_seed` and computed `swiss_number` remain in the witness
- Federation nodes see only commitment transitions
- No node can derive swiss numbers without the witness

### 4. Can We Fix This for Hosted Cells?

The four options ranked:

**Option C (Accept it) is correct.** The federation IS your trusted vat. The alternative formulations have fundamental problems:

- Option A (encrypt to recipient): The federation must be able to ROUTE messages to the cell. If it can't look up the swiss table, it can't deliver enlivened capabilities. This breaks the fundamental CapTP message delivery model.
- Option B (commitment scheme): Same problem -- the executor needs to verify the swiss number to create the routing entry. If it can't access the table, it can't execute EnlivenRef.
- Option D (single designated node): This defeats the purpose of replication for fault tolerance. That node becomes a single point of failure AND trust.

**The real fix is architectural**: If you need intra-federation capability secrecy, the cell should be SOVEREIGN. That is the entire purpose of the sovereign/hosted distinction.

### 5. EnlivenRef Interaction

- `EnlivenRef` takes `swiss_number` as a parameter in the Effect VM (sovereign path)
- For sovereign cells: the swiss number is in the proof witness, not visible
- For hosted cells: `EnlivenRef` is not an effect in the turn -- it is an internal executor operation triggered by an incoming CapTP message
- **Can someone front-run enliven?** Only if they know the swiss number AND can submit a turn to the federation before the legitimate presenter. For hosted cells, the federation validates the presenter's identity. For sovereign cells, the swiss number is never exposed on-chain.

### 6. Goblins Comparison

In Spritely/Goblins:
- The vat maintains swiss tables internally
- The vat is a single process -- no replication
- Swiss numbers are never visible outside the vat

In pyana:
- The federation maintains swiss tables via replicated execution
- All N nodes are "the vat" collectively
- Swiss numbers are visible to all N nodes (equivalently: to the vat)
- Swiss numbers are NOT visible outside the federation

**The security boundary is identical: vat boundary = federation boundary.** The N-node replication does not weaken the guarantee compared to single-process Goblins.

### 7. The Real Question Answered

> Is a hosted cell's capability system only secure against EXTERNAL adversaries? Within the federation, is there capability security at all?

**Correct. For hosted cells, capability security is ONLY against external adversaries.** Within the federation, there is no capability isolation between cells -- the executor has full access to all state of all hosted cells.

This is identical to Goblins: the vat has full access to all objects within it. Object capability security in Goblins prevents OBJECTS from accessing each other without authority -- it does not prevent the VAT from accessing objects. The vat is the trusted computing base.

In pyana: the federation has full access to all hosted cells within it. CapTP capability security prevents CELLS from accessing each other without authority -- it does not prevent the FEDERATION from accessing cells. The federation is the trusted computing base.

**This is not a bug. This is the correct architecture.**

## The Privacy Spectrum

| Cell Type | Swiss Secret From... | Capability Security Against... |
|-----------|---------------------|-------------------------------|
| Hosted (unencrypted turn) | External observers, other federations | Other cells in same federation, external parties |
| Hosted (encrypted turn) | External observers, other federations, non-validator nodes | Other cells, external parties |
| Sovereign | Everyone including hosting federation | Everyone including hosting federation |

## Minimal Fix Recommendation

No fix is needed for the current architecture. The system correctly implements:

1. **Hosted cells**: Federation as trusted vat. Swiss numbers are vat-internal state. No capability security against the federation itself (by design).

2. **Sovereign cells**: Self-sovereign proof-carrying execution. Swiss numbers proven inside STARK witness. Full capability security against everyone including the hosting federation.

**The user's escape hatch is already built: make the cell sovereign.** The `MakeSovereign` effect (turn/src/action.rs line 545) transitions any hosted cell to sovereign mode, at which point its SwissTable entries become private (proven via STARK, never revealed to the federation).

## One Genuine Improvement

There IS one legitimate improvement that would strengthen the system:

**Remove `random_seed` from `compute_effects_hash` for `ExportSturdyRef`.** Currently the effects_hash includes ALL parameters. While Poseidon2 makes this safe (preimage resistance), a defense-in-depth approach would exclude secret material from the hash entirely. The effects_hash exists to bind the EFFECTS to the proof -- it does not need to include the randomness used to derive the swiss number.

Instead, the effects_hash should include the OUTPUT (the computed swiss number) rather than the INPUT (random_seed + counter). This way:
- The proof still proves correct derivation (the constraint enforces `swiss = hash(cell_id, hash(random_seed, counter))`)
- The effects_hash binds to the swiss number being exported (not the randomness)
- Even if Poseidon2 were somehow weakened, the random_seed remains protected

This is a minor defense-in-depth change, not a security-critical fix.

## Summary

The architecture is sound. The concern was based on a misunderstanding of the data flow:

1. `random_seed` is NEVER a public input -- it is inside the Poseidon2 effects_hash preimage (sovereign) or never in the turn at all (hosted)
2. The federation knowing swiss numbers for hosted cells is architecturally correct (federation = vat)
3. Sovereign cells are fully private (STARK witness hides all CapTP secrets)
4. The only improvement is defense-in-depth: hash the swiss number OUTPUT into effects_hash instead of the random_seed INPUT
