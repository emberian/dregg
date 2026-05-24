# SDK-Consensus Demo (no MCP)

Sister demo to [`demo/two-ai-handoff`](../two-ai-handoff). The two-AI demo speaks
**MCP over stdio** — a thin RPC layer on top of `pyana-node`. This demo bypasses
MCP and exercises the lower-level pyana pathways directly, so a regression
in (for example) the wire codec or the federation consensus loop shows up here
*without* having to also drag MCP into the picture.

## What it exercises (vs the MCP demo)

| Pathway                              | MCP demo                          | This demo                                                                                          |
|--------------------------------------|-----------------------------------|----------------------------------------------------------------------------------------------------|
| Agent identity                       | `pyana_create_agent` MCP tool     | `pyana_sdk::AgentWallet::new()` directly                                                          |
| Federation                           | implicit (`pyana-node mcp`, solo) | `pyana_federation::Federation::new(&[3 nodes])` + a real `run_consensus_round`                    |
| Attested root                        | not surfaced                      | `FederationNode::get_attested_root()` → postcard to disk → re-load → `is_valid(&fed_keys)`        |
| Turn submission                      | `pyana_grant_capability` MCP tool | `pyana_turn::TurnExecutor::execute(&turn, &mut ledger)` against an in-memory `Ledger`             |
| Turn signing                         | inside the node                   | `AgentWallet::sign_turn` on the caller side                                                       |
| Receipt chain                        | `pyana_get_receipt_chain` MCP     | `AgentWallet::append_receipt` + `verify_receipt_chain(wallet.receipt_chain())`                    |
| Capability handoff                   | `pyana_create_bearer_cap` MCP     | `captp::handoff::{HandoffCertificate, HandoffPresentation, validate_handoff}` + `SwissTable`      |
| Wire framing                         | never seen                        | `pyana_wire::codec::{encode, decode}` round-trips `WireMessage::AttestedRoot` + `PresentHandoff`  |

## How to run

```bash
cargo run -p pyana-sdk-consensus-demo
```

A successful run prints six checked-off pathways and writes the persisted
`attested-root.postcard` artifact under `$TMPDIR/pyana-sdk-consensus-demo/`.

If `cargo build` fails because a sibling cargo invocation holds the lock, retry
after 60 s (matches the no-worktree concurrent-cargo policy).

## Scope

This is a **scaffolding-quality** demo — its job is to prove the SDK / federation /
wire / captp surface area can be wired together end-to-end without MCP. It is
deliberately single-process and single-threaded; the wire codec is exercised
via an in-memory round-trip rather than over a real TCP connection.

### Not in scope

- Real cross-process TCP between two `SiloServer`s (would require a tokio
  runtime and TLS setup, which is the next step up from this scaffold).
- Effect VM STARK proofs (`turn.execution_proof = None`). The MCP demo has the
  same gap today; see `demo/two-ai-handoff/README.md` blockers #4–#6.
- Federation epoch reconfiguration (see `demo-agent/examples/federation_bootstrap.rs`
  for that pathway).

### Known gap surfaced by this demo

`AttestedRoot::is_valid(&fed_keys)` returns `false` for federation-produced
attested roots. The federation populates `quorum_signatures` with **consensus
vote** signatures (over `QuorumCertificate::vote_message`), but
`AttestedRoot::is_valid` expects signatures over the AttestedRoot's own
`signing_message`. The constant-size `ThresholdQC` path is the intended
cross-verification mechanism, but `update_attested_root` only populates it when
`aggregate_qc` is set, which the in-memory consensus round currently does not
do. The demo asserts `is_structurally_valid()` and explicitly records the
crypto-path gap so it shows up in CI rather than hiding. The
`demo-agent/examples/federation_bootstrap.rs` example panics on the same
mismatch in its step 6 today.

## Follow-up to make this a "WHOLE capability system in motion" exercise

The demo as committed validates the *structural* path (every API connects to
every other API correctly). To upgrade it to a strong assertion of correctness:

1. **Real TCP transport.** Run two `pyana_wire::server::SiloServer` instances on
   loopback and have one present the `HandoffCertificate` to the other over a
   real socket (instead of the in-memory codec round-trip).
2. **AgentWallet → captp::handoff bridge.** Today the demo derives a fresh
   `ed25519_dalek::SigningKey` for the handoff introducer because `AgentWallet`
   does not expose its underlying signing key. A small accessor (or a
   `wallet.create_handoff_certificate(...)` convenience) would let the same
   wallet identity that signed the turn also sign the cert. Pushed to a
   follow-up per the task instructions (don't modify production crate APIs).
3. **Effect VM proof.** Once `convert_turn_effects_to_vm` projects `Transfer`
   honestly, set `turn.execution_proof = Some(proof)` and verify it at the
   federation boundary.
4. **Receipt chaining across the handoff.** Currently Alice's transfer receipt
   chain and the handoff are independent; chain them via
   `previous_receipt_hash` so the cert binds to a specific prior commitment.
