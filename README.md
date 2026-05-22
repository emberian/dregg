# Pyana

Pyana is private, portable authorization for software agents. It lets an agent
prove it holds sufficient authority for an action without revealing who
authorized it, what else it can do, or that it is the same agent that acted
before. If you are building systems where autonomous services delegate to each
other across trust boundaries, this is the authorization layer.

## What it looks like

```rust
use pyana_sdk::{AgentWallet, VerificationMode};
use pyana_token::Attenuation;

let mut wallet = AgentWallet::new();
let root = wallet.mint_token(b"my-service-root-key-32-bytes!!!!", "storage");

// Narrow the token: read-only, 1000-call budget, expires in 1 hour
let restricted = wallet.attenuate(&root, &Attenuation {
    services: vec![("storage".into(), "r".into())],
    not_after: Some(now + 3600),
    ..Default::default()
}).unwrap();

// Present to a verifier who learns nothing except "authorized: yes"
let proof = wallet.authorize(&restricted, &request, VerificationMode::FullyPrivate)?;
```

The token is an HMAC-chained macaroon. Attenuation is local and offline -- no
round-trip to the issuer. The proof is a STARK that covers the full Datalog
derivation chain in zero knowledge.

## Key insight

Capability tokens give you attenuate-only delegation (you can only hand out
subsets of what you hold). Zero-knowledge proofs let you exercise those
capabilities without exposing the delegation chain to the verifier. Together
they solve the agent authorization problem: give sub-agents exactly the
authority they need, let them prove it to third parties, and reveal nothing
else.

## Getting started

The tutorial at `site/docs/developers/tutorial-first-app.md` walks through a
complete working example: mint a root key, attenuate it for a customer, verify
offline, and revoke -- all in ~60 lines of Rust, no ZK required.

## Architecture

The system is organized in layers. `token` handles HMAC macaroons and typed
caveats. `cell` provides the capability-security state model (c-lists,
unforgeable references, attenuation-only delegation). `circuit` compiles
Datalog authorization rules into arithmetic constraints and proves them via a
custom BabyBear STARK. `bridge` connects token evaluation to circuit witness
generation. `sdk` wraps everything into an ergonomic wallet API. `wire` and
`node` handle network transport and BFT federation consensus. `turn` is the
atomic execution unit -- a signed action forest that modifies cell state.

## Status: Experimental

This is research software with known severe limitations. Do not use it in
production or for anything security-critical.

Known issues include: custom STARK with non-standard security parameters,
app-level code that has only recently been wired to real proof verification,
git-pinned unstable cryptographic dependencies, incomplete recursive proof
paths, and a codebase under active refactoring. The proof system backends
have undergone adversarial auditing this development cycle but no external
audit has been performed.

Some things work end-to-end (token minting, attenuation, STARK presentation,
assisted Pickles recursion). Many things are partially implemented or in
active development (Mina-equivalent recursion, STARK-in-Pickles compression,
browser extension, on-chain settlement). The node daemon is functional but
not hardened for adversarial network environments.

## Further reading

- Design rationale: `docs/design-rationale.md`
- Protocol specification: `docs/protocol-sketch.md`
- Agent authorization use case: `docs/agent-authorization.md`
- Recursive proof architecture: `docs/recursive-proof-architecture.md`

## License

MIT OR Apache-2.0
