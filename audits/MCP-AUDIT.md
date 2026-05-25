# MCP Tool Surface Audit

Audit of the pyana MCP tool surface defined in `node/src/mcp.rs` against the
canonical demo specified in `dev-philosophy/06-the-real-demo.md` and the
MCP-first principle in `dev-philosophy/01-north-star.md`.

Status legend:

- **REAL** — fully functional, produces real state mutations / real proofs /
  real receipts.
- **PARTIAL** — works for the happy path but is missing pieces (cell
  registration, ledger integration, error handling, etc).
- **SCAFFOLDED** — returns success but the underlying work doesn't actually
  happen (or returns mock data).
- **FAIL-CLOSED** — explicitly returns an error indicating the tool isn't
  implemented.

## Audit table

| Tool | Status | Notes |
|---|---|---|
| `pyana_get_status` | REAL | Reads live `store.latest_attested_root()`, revocation/note counts, peer count. No mock anywhere. |
| `pyana_create_agent` | SCAFFOLDED | Generates an Ed25519 keypair with `pyana_sdk::AgentWallet::new()` and returns the pubkey, but **does not insert a `Cell` into the ledger**. The created identity is ephemeral — `pyana_read_cell` on its derived id reports `found: false`. The CellProgram, balance, c-list spoken about in the philosophy doc never come into existence. |
| `pyana_authorize` | PARTIAL | Iterates `wallet.tokens()` and checks `verify_token` against the requested action/resource. Works against the operator's wallet, but doesn't generate a ZK proof in any mode (the `mode` parameter is ignored once the boolean answer is computed). |
| `pyana_submit_turn` | PARTIAL | Builds a Turn with an empty effect list, signs it with the operator's wallet, executes through `TurnExecutor`, persists the receipt, emits the event, and gossips. The "happy path" of recording a turn is real, but the action has `Authorization::Unchecked`, no effects, no preconditions — every submit is a no-op turn that costs computrons but mutates nothing. Useful for chaining receipts, not for doing work. |
| `pyana_grant_capability` | REAL | Builds a turn containing `Effect::GrantCapability` with a real `CapabilityRef`, executes through `TurnExecutor::execute`, persists the receipt to the wallet chain, emits events, and gossips. Turn rejection paths are surfaced. The grant lands in the target cell's `CapabilitySet` *if the target cell exists in the ledger*. (See "Wire-through caveats" below — cells created by `pyana_create_agent` won't exist, so grants will fail.) |
| `pyana_revoke_capability` | REAL | Builds and executes `Effect::RevokeCapability` for the operator's own cell. Same execution/gossip pattern as grant. Effective when the operator cell exists in the ledger. |
| `pyana_post_intent` | REAL | Builds a real `Intent`, stores it in `state.intent_pool` (bounded by `MAX_NODE_INTENT_POOL`), emits an `Intent` event. No mock. |
| `pyana_fulfill_intent` | PARTIAL | Looks up the intent, builds a `FulfillmentWithPredicates`, calls `pyana_intent::fulfillment::execute_fulfillment_flow` against the live executor and ledger. Real where it works. Fails closed with a clear message when the intent has predicate requirements (predicate proofs must be generated separately). |
| `pyana_delegate` | REAL | Calls `wallet.delegate()` (token-level attenuation produces a real `DelegatedToken`), records the delegation on-ledger via `Effect::GrantCapability`. Executes, gossips. |
| `pyana_check_capabilities` | REAL | Reads `wallet.tokens()`, `wallet.receipt_chain_length()`, returns a real snapshot. |
| `pyana_read_cell` | PARTIAL | Reports `found` correctly via `ledger.get()` but hard-codes `balance: null`. The HTTP `get_cell_detail` endpoint exposes balance, nonce, capability_count, delegate, program — the MCP analog drops all of that. |
| `pyana_get_receipt_chain` | REAL | Reads the operator wallet's real receipt chain, serializes turn hashes, pre/post state, timestamps, computron counts. |
| `pyana_seal_data` | REAL | X25519 + ChaCha20-Poly1305 with ephemeral key. Real forward secrecy, real KDF. |
| `pyana_unseal_data` | REAL | Mirrors `seal_data` correctly, deriving the wallet's X25519 secret from its private signing material (not the public key — comment explicitly flags this). |
| `pyana_bridge_note` | PARTIAL | Builds a real `Effect::BridgeLock`, executes it. But `spending_proof: vec![]` is a placeholder — the executor will accept it (no proof verification in the executor for BridgeLock today), so a "real" bridge that another federation would honor isn't produced. |
| `pyana_make_sovereign` | PARTIAL | Calls `ledger.register_sovereign_cell(cell_id, blake3(cell_id_bytes))`. The registration happens, the federation moves to commitment-only for that cell. But the initial commitment is just `blake3(cell_id)` — not derived from the actual cell state — so it's symbolic. The HTTP `post_register_cell` analog uses a signed message and a caller-supplied commitment; this MCP version skips both. |
| `pyana_peer_exchange` | SCAFFOLDED | Creates an in-memory `PeerExchange` instance, calls `create_transition`, hashes the transition. The result is never persisted, never advances the ledger, never propagates to a peer. The "transition_hash" is a value the caller can show off but it isn't bound to any real ledger state. |
| `pyana_compress_history` | REAL | Runs `prove_ivc_stark` over the real receipt chain (with a synthesized monotone root sequence), runs `verify_ivc_stark` on the resulting proof. Real STARK, real verifier. The synthesized state-root sequence is symbolic, but the proof object is genuine. |
| `pyana_create_bearer_cap` | PARTIAL | Signs a delegation message `target ‖ bearer_pk ‖ expires_at ‖ perm_tag` with the operator's gossip signing key. The signature is real. The `bearer_cap_id` is real. But no swiss-number / no swiss-table entry / no `pyana://` URI / no `HandoffCertificate` — the OCAP three-party handoff isn't here. |
| `pyana_exercise_bearer_cap` | PARTIAL | Constructs a real `BearerCapProof` with `DelegationProofData::SignedDelegation`, builds a turn with `Authorization::Bearer`, executes through `TurnExecutor`. The executor *does* verify the bearer cap (via `verify_bearer_cap`) — this path is real. Missing: empty effects array (the bearer holder can't actually do anything via this MCP tool); doesn't accept user-supplied effects parameter; no swiss-number consumption (replayable until expiry). |
| `pyana_deploy_factory` | SCAFFOLDED | Builds a `FactoryDescriptor`, computes its hash, **but never inserts it into any registry**. Returns success with the hash. The next `pyana_create_from_factory` call works because that function doesn't check that the factory was deployed. |
| `pyana_create_from_factory` | SCAFFOLDED | Derives a child cell id from `factory_vk ‖ name ‖ nonce`, optionally registers as sovereign (commitment-only). Does not check that the factory exists, does not produce a creation proof, does not insert a hosted cell. The "provenance" object returned has `proof_hash: None`. |
| `pyana_verify_provenance` | PARTIAL | Checks ledger for hosted/sovereign registration and runs `provenance.verify_derivation`. The verifier is real, but cells from `pyana_create_from_factory` rarely show up because creation is itself scaffolded. |
| `pyana_prove_sovereign_turn` | REAL | Parses effects into `pyana_circuit::effect_vm::Effect`, generates a real trace, builds an `EffectVmAir`, runs `pyana_circuit::stark::prove`. Returns a real serialized STARK proof. The initial state `(1000, 0)` is hardcoded, so the proof is over a fictional starting balance — fine for `verify_sovereign_proof` round-trip but not bound to any actual cell state. |
| `pyana_verify_sovereign_proof` | REAL | Deserializes the postcard STARK proof, runs `pyana_circuit::stark::verify` against `EffectVmAir`. Real verification. |
| `pyana_create_stealth_address` | PARTIAL | Generates an ephemeral X25519 keypair, performs DH with the recipient's view pubkey, derives a scalar via BLAKE3. The "one-time address = spend_pk XOR scalar" line is explicitly simplified ("full impl uses curve addition" in the comment). The derived address isn't curve-valid; a recipient cannot actually spend with it. |
| `pyana_private_transfer` | PARTIAL | Computes a Pedersen-style commitment (BLAKE3-derived, not curve-based), builds a `NoteCreate` effect, executes through `TurnExecutor`. The note lands in the note pool. But: `value: 0` and `asset_type: 0` (hidden in commitment — fine), `range_proof: None` (the executor will accept zero-value notes without complaint), `encrypted_note: vec![]` (recipient can't actually decrypt the amount). |
| `pyana_encrypt_intent` | REAL | Calls `EncryptedIntent::create`, stores in `state.encrypted_intent_pool`. Real SSE encryption. |
| `pyana_prove_predicate` | REAL | Builds a `PredicateWitness`, calls `pyana_circuit::prove_predicate`. Real STARK predicate proof generation. The fact_hash derivation truncates to 16 bits which is poor entropy, but the proof object itself is real. |
| `pyana_compose_proofs` | SCAFFOLDED | Hashes the proofs together with a derive-key context, returns the hash. Does **not** verify any of the input proofs, does not produce a composed proof object that a verifier could check. The `valid` field is hardcoded `true` for every supported mode. |
| `pyana_get_blocklace_status` | REAL | Reads live federation state from `state`. |
| `pyana_get_constitution` | PARTIAL | Returns the participant set and a computed BFT threshold. Real data, but the threshold computation (`n/3 + 1`) is an editorial guess — pyana doesn't enforce a particular threshold here, so this number is informational only. |
| `pyana_propose_membership` | SCAFFOLDED | Builds a `MembershipProposal` enum locally, computes a proposal_id hash, **drops the proposal on the floor**. Returns success. No persistence, no propagation, no voting machinery touched. |
| `pyana_check_resource_budget` | REAL | Reads from `state.budget_coordinators` and the silo state. Real numbers when a coordinator exists. |
| `pyana_debit_shared_resource` | REAL | Calls `state.try_budget_debit()` which is the live bounded-counter coordination logic. |
| `pyana_list_auctions` | PARTIAL | Filters `state.intent_pool` for gallery-shaped intents. Real subset, but there's no actual auction object — it conflates intents with auctions. |
| `pyana_place_bid` | PARTIAL | Computes a real commitment `BLAKE3(bidder ‖ amount ‖ nonce)`, posts an intent with the commitment as resource. The intent really lands. There's no auction state machine on the other side. |

## Two-AI handoff demo readiness

The demo (philosophy doc 06) requires this minimal tool set:

1. `pyana_create_agent` — SCAFFOLDED (needs ledger insertion)
2. `pyana_grant_capability` — REAL (but needs (1) so target cell exists)
3. `pyana_create_bearer_cap` — PARTIAL (no swiss-table / no URI yet, but the
   delegation signature is real)
4. `pyana_exercise_bearer_cap` — PARTIAL (real executor path, but no effects,
   so the bearer can't actually do anything)
5. `pyana_submit_turn` — PARTIAL (works for empty turns; needs effect support
   for the bearer to actually transfer)
6. `pyana_read_cell` — PARTIAL (`found` works; balance/etc. dropped)
7. `pyana_get_receipt_chain` — REAL

### Demo blockers (in order)

1. **Cell creation has no ledger side-effect.** Without it, `pyana_grant_capability` will fail because the target cell isn't in the ledger.
2. **`pyana_read_cell` drops state.** Alice and Bob can't observe the balance changing.
3. **`pyana_exercise_bearer_cap` has no effects.** Bob can hold a valid cap but can't move anything.
4. **`pyana_submit_turn` has no effects parameter.** Same issue — the bearer can't actually do work.
5. **No `pyana://` URI handling.** The handoff in step 5 of the demo (Alice → Charlie verifier → Bob enliven) needs a URI form. Out of scope for the first wire-through pass, but the demo doc calls it out.

## Anti-patterns observed (per philosophy doc anti-patterns)

- Some tools (`pyana_compose_proofs`, `pyana_propose_membership`,
  `pyana_peer_exchange`, `pyana_deploy_factory`) return success without doing
  the work. These are exactly the "looks good on the wire, isn't real" pattern
  the philosophy doc names. They should either fail-closed or be made real.
- `pyana_authorize` `mode: "trusted"` is the trusted-hash anti-pattern called
  out in the demo doc; it returns a boolean derived from token lookup, not a
  proof.
