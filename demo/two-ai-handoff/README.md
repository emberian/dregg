# Two-AI Capability Handoff Demo — Silver-Vision Edition

End-to-end demo of pyana's Silver-Vision substrate pieces, driven by two
simulated AI processes (`alice` and `bob`), verified by an
independent process (`charlie`) shelling to the structurally-independent
`pyana-verifier` binary.

## What this demo demonstrates

1. **Canonical capability handoff** — Alice (introducer) signs a
   `HandoffCertificate` naming Bob; Bob signs a `HandoffPresentation`
   over it; both signatures are verified end-to-end by Charlie.

2. **`Authorization::CapTpDelivered`** — Bob assembles a canonical
   `Turn` carrying `Authorization::CapTpDelivered { handoff_cert,
   introducer_pk, sender_pk, sender_signature }`. The `sender_signature`
   binds Bob's identity to the cert + the action's effects via the
   canonical `captp_delivered_signing_message`. Charlie reruns the
   executor's `verify_captp_delivered` checks (introducer-sig on cert,
   sender-sig on signing message, pk equalities, cert-freshness) and
   reports the verdict. A tampered variant (single byte flipped in the
   sender signature) is required to **reject** — this is part of
   `expected.json:must_not_pass`.

3. **`SovereignCellWitness`** — Alice produces the post-soundness-sweep
   shape of a sovereign-cell witness (Ed25519 signature over the canonical
   signing message including `sequence` and `effects_hash`). Charlie
   verifies both the witness and a tampered variant (post-state commitment
   byte-flipped, which must reject).

4. **Slot caveats (`StateConstraint::WriteOnce`)** — A `CellProgram::Predicate`
   carrying `WriteOnce { index: NAME_SLOT }` + `Monotonic { index: EXPIRY_SLOT }`
   is exercised end-to-end via `CellProgram::evaluate`:
     - first registration accepted
     - re-registration with a different value **rejected** (`must_not_pass`)
     - renewal (bumping the monotonic expiry slot, unchanged name)
       accepted

5. **γ.2 bilateral binding** — A `BilateralBundle` is assembled for a
   single `Effect::Transfer { from: alice, to: bob, amount: 100 }`, with
   one fabricated `WitnessedReceipt` per cell carrying the γ.2 PI
   layout. Charlie shells to `pyana-verifier bilateral-pair <bundle>`
   to confirm cross-cell pair-verification (the schedule's
   transfer-id-derived OUTGOING_TRANSFER_ROOT on Alice matches the
   INCOMING_TRANSFER_ROOT on Bob, with `IS_AGENT_CELL` exactly 1 on
   Alice's WR and 0 on Bob's). A tampered bundle (one felt flipped in
   Alice's `OUTGOING_TRANSFER_ROOT`) **must** reject.

The demo also continues to drive Alice's grant turn and Bob's exercise
turn through `pyana-node`'s MCP layer so the receipt chain, balance
deltas, and per-turn STARK proofs are real ledger artifacts.

## How to run

```bash
cd demo/two-ai-handoff
./run.sh
```

`run.sh` builds `pyana-node`, `pyana-verifier`, and `silver-helper`. On
cargo failure it sleeps 60s and retries once (matches the no-worktree
concurrent-cargo policy).

Exit 0 ⇔ every `must_pass` assertion holds AND every `must_not_pass`
assertion was correctly rejected.

## Architecture

| Component       | Crate              | Independent? |
|-----------------|--------------------|--------------|
| `pyana-node`    | `node`             | the prover (Alice, Bob each get their own data-dir) |
| `pyana-verifier`| `verifier`         | structurally independent — links only `pyana-circuit`, `pyana-turn`, `pyana-federation`, `pyana-captp`, `pyana-types` |
| `silver-helper` | `pyana-demo` (this directory hosts `silver_helper.rs`) | the demo-side helper that assembles canonical CapTP-delivered / sovereign / γ.2 artifacts using the substrate's real types but demo-local Ed25519 keys |
| `alice.py`      | drives Alice's `pyana-node mcp` over JSON-RPC | runs in its own process |
| `bob.py`        | drives Bob's `pyana-node mcp` over JSON-RPC | runs in its own process |
| `charlie.py`    | drives `pyana-verifier` and `silver-helper` | NO MCP, NO node — pure off-disk verification |

## Files

- `run.sh` — orchestrator
- `alice.py` — Alice's MCP driver (grant + bearer-cap-create + compress-history)
- `bob.py` — Bob's MCP driver (identity + exercise)
- `charlie.py` — verifier driver (shells to `pyana-verifier` + `silver-helper`)
- `silver_helper.rs` — the demo's Rust helper binary; registered in
  `../Cargo.toml` as `[[bin]] name = "silver-helper"`
- `expected.json` — declarative `must_pass` / `must_not_pass` post-conditions
- `mcp_stdio.py` — newline-delimited JSON-RPC client for the MCP nodes
- `state/` — runtime scratch (cleaned every run)

## Documented gaps (where MCP doesn't expose substrate features yet)

These are the spots where `silver-helper` does in Rust what an MCP tool
*should* do. Each is one MCP tool away from the demo running entirely
through the node:

1. **`pyana_exercise_handoff_cert`** — would build a Turn with
   `Authorization::CapTpDelivered` via the MCP layer. Today, the
   existing `pyana_exercise_bearer_cap` uses `Authorization::Bearer`.

2. **`pyana_submit_sovereign_turn`** — would let an MCP client submit
   a Turn whose `sovereign_witnesses` map carries a cclerk-signed
   `SovereignCellWitness`. Today, `pyana_make_sovereign` only registers
   the cell as sovereign — there's no MCP path to land a witness-carrying
   turn.

3. **`pyana_install_cell_program`** — would let an MCP client attach a
   `CellProgram::Predicate(Vec<StateConstraint>)` to a cell so the
   executor enforces the slot caveats on every turn. Today, the
   constraint enforcement code (`cell/src/program.rs::evaluate`) is
   public but no MCP tool wires it onto a live cell.

4. **Per-cell `WitnessedReceipt` emission** — `pyana_exercise_bearer_cap`
   today produces a single agent-side WR. For γ.2 bilateral verification
   we need *one WR per touched cell*. This depends on Stage-7-γ.0
   per-cell proof emission landing throughout the executor's commit
   path; until then, `silver-helper` fabricates the WRs from the canonical
   `ExpectedBilateral` schedule (the verifier accepts them because the
   PI layout is exactly what a real prover would emit).

These gaps are tracked in `expected.json:documented_gaps`. The demo
passes today; closing each gap collapses one `silver-helper` call into
a single MCP invocation.

## What the demo deliberately does NOT prove

(unchanged from prior README; Silver-Vision boundary)

- Federation BFT consensus (single-node)
- Cross-federation bridging (single federation; see
  `SILVER-VISION-E2E-VERIFICATION.md` for the cross-fed sibling demo)
- Scale (single transfer)
- Privacy (Charlie sees what Alice and Bob do — that's the point)
