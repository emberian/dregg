# @pyana/sdk

TypeScript SDK for the pyana distributed authorization system.

Wraps the `pyana-wasm` module into ergonomic, type-safe APIs for token management, zero-knowledge proofs, Merkle trees, Datalog authorization, and full runtime simulation.

## Installation

```bash
npm install @pyana/sdk pyana-wasm
```

## Quick Start

```ts
import init from "pyana-wasm";
import { PyanaClient } from "@pyana/sdk";

// Initialize WASM and create client
const wasm = await init();
const client = await PyanaClient.init(wasm);

// Mint a token
const token = await client.cclerk.mint("api-gateway");
console.log(token.token); // "em2_..."

// Attenuate (restrict) the token
const restricted = await client.cclerk.attenuate(token.token, {
  service: "api-gateway",
  actions: "read",
  expiresSecs: 3600,
});

// Verify
const result = await client.cclerk.verify(restricted.token, { action: "read" });
console.log(result.allowed); // true
```

## Modules

### Cipherclerk (Token Lifecycle)

```ts
const cclerk = await AgentCipherclerk.create(wasm);
const token = await cclerk.mint("my-service");
const attenuated = await cclerk.attenuate(token.token, { actions: "read" });
const verified = await cclerk.verify(attenuated.token, { action: "read" });
```

### STARK Proofs

```ts
const engine = new ProofEngine(wasm);
const proof = await engine.generateStarkProof(42, 4);
const valid = await engine.verifyStarkProof(proof.proof_json);
```

### Predicate Proofs (ZK Comparisons)

```ts
// Prove age >= 18 without revealing exact age
const proof = await engine.generatePredicateProof({
  predicateType: "gte",
  privateValue: 25,
  threshold: 18,
  attributeKey: "age",
  stateRoot: 12345,
});
```

### Merkle Trees

```ts
const tree = new MerkleTree(wasm);
const root = await tree.computeRoot(["alice", "bob", "carol"]);
const proof = await tree.proveMembership(["alice", "bob", "carol"], "bob");
```

### Datalog Authorization

```ts
const evaluator = new PredicateEvaluator(wasm);
const result = await evaluator.evaluate(
  [
    { predicate: "member", terms: ["alice", "admin"] },
    { predicate: "permission", terms: ["admin", "read"] },
  ],
  { action: "read" }
);
```

### Runtime Simulation

```ts
const runtime = client.createRuntime();

const alice = await runtime.createAgent("alice", 1000);
const bob = await runtime.createAgent("bob", 500);

// Transfer
const result = await runtime.executeTurn(alice.agent_index, [
  { type: "transfer", to: bob.cell_id, amount: 100 },
]);

// Federations
const fed = await runtime.createFederation("testnet", 4);
await runtime.proposeBlock(fed.fed_index, ["event1", "event2"]);

// Intents
const intent = await runtime.createIntent(
  alice.agent_index,
  "Need",
  [{ action: "read", resource: "docs/*" }],
  [{ Service: "storage" }],
  "",
  1716000000
);

runtime.destroy();
```

## API Reference

| Class | Purpose |
|-------|---------|
| `PyanaClient` | Main entry point combining all subsystems |
| `AgentCipherclerk` | Token mint/attenuate/verify |
| `TokenOps` | Fold chains, BLAKE3 hashing, intent IDs |
| `ProofEngine` | STARK proofs, predicates, Schnorr, garbled circuits |
| `MerkleTree` | Root computation, membership/non-membership proofs |
| `PredicateEvaluator` | Datalog authorization engine |
| `PyanaRuntime` | Full distributed system simulation |

## License

MIT
