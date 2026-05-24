# pyana-observability

Seed crate for the in-browser **turn explorer**.

## What it does

A standalone binary that constructs a one-Turn-one-Transfer scenario, runs the
real `TurnExecutor` on an in-memory `Ledger`, then **separately** generates the
Effect VM trace + STARK proof for the same transition, verifies it, and emits
**everything** as a single JSON document on stdout.

The output is the proposed wire format an off-line explorer would consume to
"replay" any turn step by step.

## Run

```
cargo run -p pyana-observability
```

The entire JSON document is pretty-printed to stdout. Pipe through `jq` or
redirect to a file:

```
cargo run -p pyana-observability > /tmp/trace.json
cargo run -p pyana-observability | jq '.air.trace_width'
```

## JSON schema (v1)

Top-level keys:

| field              | shape                                                                          |
| ------------------ | ------------------------------------------------------------------------------ |
| `schema_version`   | `1`                                                                            |
| `schema_name`      | `"pyana-observability-turn-trace-v1"`                                          |
| `turn`             | `{ agent, nonce, fee, memo, valid_until, action_count, effects[], turn_hash }` |
| `pre_state`        | array of cell views (cell_id, balance, nonce, state_commitment, ...)           |
| `post_state`       | same shape as `pre_state`                                                      |
| `receipt`          | full `TurnReceipt` flattened: turn_hash, forest_hash, pre/post state_hash, effects_hash, timestamp, action_count, computrons_used, federation_id, finality, receipt_hash |
| `vm_effects`       | array of `effect_vm::Effect` projected for the agent cell                      |
| `air`              | `{ air_name, trace_width, trace_height, trace_first_row[], public_input_count, public_inputs[] }` |
| `proof`            | `{ air_name, trace_len, num_cols, fri_layers, query_count, pow_bits, size_bytes_json, trace_commitment, constraint_commitment }` |
| `verification`     | `{ verified, error, trace_len, public_input_count }`                           |
| `notes`            | provenance + caveats                                                           |

All 32-byte values are hex-encoded (lowercase, no `0x`). Field elements
(`BabyBear`) are emitted as raw `u32`.

## What the explorer would do with this

For each turn, the explorer can:

1. Render the Turn (effects, fee, agent) as a structured form.
2. Show pre/post diffs by cell (balance/nonce/state_commitment).
3. Display the Effect VM trace as a matrix (`trace_height` rows × `trace_width`
   cols). Highlight cells that change between rows; that is, *literally* show
   the AIR step-by-step.
4. Cross-reference: receipt's `effects_hash` ↔ effects shown ↔ `vm_effects`.
5. Verify the proof in WASM (the verifier is already pure Rust; a wasm build
   of `pyana-circuit` would let the browser independently confirm
   `verification.verified`).

## What is **not** here (yet) — follow-up

1. **One-shot demo only.** The Turn is constructed locally with a hardcoded
   single Transfer. To trace **any** turn, the executor would need to expose
   a streaming hook (`fn on_step(&mut StepEvent)`) or write a per-turn
   side-channel `EventLog`. Both touch trust-critical code (`executor.rs`)
   and want a real design conversation — out of scope for the seed crate.

2. **Effect projection duplicated.** `project_turn_effects_for_cell` mirrors
   `pyana_turn::executor::TurnExecutor::convert_turn_effects_to_vm`, which
   is `pub(self)` (private to `impl TurnExecutor`). Widening visibility
   would couple the trust-critical executor's call shape to an observability
   concern. The future "any-turn trace" tool will either:

   - extract the projection into a `pub fn` in `effect_vm::projection`, or
   - have the executor itself emit the projected vec into a side-channel
     during execution.

3. **Hosted vs. sovereign.** A hosted-cell turn (which this demo is) does
   **not** actually carry a STARK proof through the executor — it goes the
   classical path. We **separately** generate the Effect VM trace to demo
   the pathway. For sovereign cells the executor itself verifies a real
   STARK proof; an explorer fed those turns would have the proof
   **already**.

4. **Trace rendering.** Only `trace_first_row` is emitted. For step-by-step
   replay the explorer wants `trace[row]` for every row. Trivial extension
   (loop over rows) — left out to keep the demo output skim-readable.

5. **Inter-cell view.** Only the agent's effect projection is emitted; a
   transfer also has a recipient-side projection. The explorer would want
   one Effect-VM-trace block **per touched cell**.

## Code-touch report

- **No production code modified.** No `pub` widening, no instrumentation
  hooks, no executor changes.
- The only file outside `observability/` touched is the workspace root
  `Cargo.toml` (added `observability` to `[workspace.members]`).
