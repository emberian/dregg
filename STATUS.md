# dregg — status (code-verified)

This file is **ground truth, derived from code and from commands that actually run** —
not from design narrative. The many `*.md` design/audit documents now under
[`docs-old/`](docs-old/) are mid-development aspirational notes of *unknown current
validity*; do not treat them as authoritative. When this file and a design doc
disagree, the code wins, then this file, then nothing else.

_Last verified against the tree on 2026-05-28._

## What builds, right now

- `cargo check -p dregg-types -p dregg-cell -p dregg-turn -p dregg-circuit -p dregg-verifier --tests`
  → **compiles clean** (warnings only; no errors).
- Test population (counts of `#[test]`/`#[tokio::test]`, not pass-rate): roughly
  **2,500 tests across the core crates** — circuit ~1040, cell ~485, turn ~450,
  storage ~214, sdk ~143, node ~85, verifier ~38, types ~33.

## Run something in ~30 seconds

Two small, **executable** examples exist precisely so the on-ramp can't rot — they
are compiled code, not prose:

### The smallest receipt chain (GitHub issue #3)

```sh
cargo run -p dregg-sdk --example hello_receipt_chain
```

Creates an agent, submits one turn with a single `Effect::SetField`, and prints the
resulting `TurnReceipt` as JSON plus the one-entry receipt chain. The printed JSON is
the canonical receipt shape to pin a dregg-compatible shim against. Source:
[`sdk/examples/hello_receipt_chain.rs`](sdk/examples/hello_receipt_chain.rs).

Honest caveats this example makes visible: on a local, federation-less ledger the
receipt's `federation_id` is all-zero and `executor_signature` is `null` (no executor
attestation in a single-process run).

### The predicate language (GitHub issue #1)

```sh
cargo run -p dregg-cell --example predicate_language
```

Constructs real `CellProgram::Predicate(vec![StateConstraint::…])` programs and runs
them through `CellProgram::evaluate(new, old, ctx)` — the same call the executor makes
before committing — against accepting and rejecting transitions. Includes akapug's
"drop messages whose audience field isn't self" case via `FieldEquals` and `AnyOf`.
Source: [`cell/examples/predicate_language.rs`](cell/examples/predicate_language.rs).

Canonical code locations: `StateConstraint`, `CellProgram`, and `CellProgram::evaluate`
all live in `cell/src/program.rs`; `CellState` (8 state slots) in `cell/src/state.rs`.

### Other real binaries

`dregg-node` (`cargo run -p dregg-node -- run`, plus `init`/`status`/`mcp`/`genesis`/
`register-federation`/`relay`), the `dregg` CLI, `dregg-demo-agent`, and `dregg-verifier`.
The node MCP server (`dregg-node mcp`) registers **46 tools** (e.g. `dregg_create_agent`,
`dregg_submit_turn`, `dregg_get_receipt_chain`) — see `node/src/mcp.rs`.

## Proof / verification mode (GitHub issue #2 — honest answer)

There is **no `DREGG_PROOF_MODE` env var or config knob today.** What exists in code:

- A `VerificationMode` enum in the SDK (`sdk/src/cipherclerk.rs`: `Trusted`,
  `SelectiveDisclosure { reveal }`, `FullyPrivate`) and a parallel one in `intent`
  (`Trusted`/`Selective`/`Private`). The SDK authorization path dispatches all three.
- The node's MCP path currently uses `VerificationMode::Trusted` (cleartext + trace,
  no STARK). So the README's "Trusted by default" is *behaviorally* true for the node,
  but it is hardcoded, not operator-selectable.

Wiring an explicit, uniformly-honored mode selector is tracked, not done.

## Known gaps (pointers, not promises)

Soundness/correctness debt is tracked in the task list and in `docs-old/SILVER-DEBT.md`
(archived; verify any specific claim against code before relying on it). Active items
include cross-federation attested-root threshold handling, intent-fulfillment
body-membership binding, and queue FIFO completeness.

## On the archived docs

The `docs-old/` and `docs/` trees contain design rationale, audits, and aspirational
plans accumulated across many development sessions and several different authors/models.
They are kept for history (timestamps preserved) and can be genuinely useful as *design
intent*, but they routinely describe things as finished that are partial, and miss
features that already shipped. Trust the code.
