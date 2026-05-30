# `dregg` - Dragon's Egg

Dragon's Egg is my experiment in the metatheory of constructive knowledge, and a direct expression of my original impetus to build <https://rbg.systems>. Maybe Dragon's Egg will be a Robigalia userspace. In the meantime, here's what the LLMs have to say about it:

(end-of-human-text)

> **There are two layers here, and it matters which you're looking at.**
>
> 1. **dregg1 — the running Rust fabric** (~60 crates, this repo's top level). Integration-complete:
>    a real STARK proof system, CapTP, a blocklace, programmable queues, intents. It *works* —
>    but its security is **trust-based at the semantic core** (authorization is plain Rust outside
>    any proof; the per-turn surface is step-*incomplete*). This is the **Silver Vision**:
>    everything connected, not yet verified from first principles.
> 2. **dregg2 — the verified successor, in Lean 4** ([`metatheory/`](metatheory/)). The semantic
>    core *as proof*: the metatheory of constructive knowledge made executable and machine-checked,
>    l4v-shaped (Abstract Spec → factored middle layer → executable Design Spec → refinement). This
>    is where the system is being **re-derived honestly** — and it is the present focus.
>
> **Start with dregg2 if you want the ideas:** [`metatheory/CONSTRUCTIVE-KNOWLEDGE.md`](metatheory/CONSTRUCTIVE-KNOWLEDGE.md)
> (the actual metatheory), then [`metatheory/README.md`](metatheory/README.md) (the Lean
> architecture), then [`docs/rebuild/REORIENT.md`](docs/rebuild/REORIENT.md).
> **Start with dregg1 if you want to run something:** [`STATUS.md`](STATUS.md) +
> `cargo run -p dregg-sdk --example hello_receipt_chain`. The design `*.md` once at the repo root
> now live in [`docs-old/`](docs-old/) and are **not** authoritative — trust the code.

## dregg2 — the metatheory, in Lean (the verified core)

A capability is **constructive knowledge**: to *hold* one is to be able to *exhibit a witness that
verifies* — never merely to assert. dregg2 builds that as theorems. The current shape (all
`lake build`-green, every `sorry` honest and in one of two declared buckets):

- **The actual metatheory** (`Metatheory.*`) — the candidate-independent logic: knowledge = a
  discharging witness exists; the verify/find asymmetry; the epistemic-boundary lattice (a ZK
  verifier learns only *acceptance*); the generative/restrictive authority duality and
  *"only connectivity begets connectivity"*; coinductive no-drift soundness.
- **The factored middle layer** (`Dregg2.Spec.*`) — a *small* set of orthogonal primitives that
  *generate* dregg1's sprawling catalogs (no flat-coproduct port): one verify-seam **`Guard`**,
  multi-domain value-monoid-parametric **`Conservation`** (value hidden yet provably conserved),
  the generative **`Authority`** graph, the attested-dual-of-creation **`Lifecycle`**, and the
  **`Hyperedge`** — *the turn is an atomic hyperedge* (a wide pullback over a shared turn-id;
  bilateral / ring / forest are incidences of one object; committing it is a decidable proof, not
  a consensus protocol — canonicity is the separate consensus layer).
- **The executable kernel + portals** (`Dregg2.Exec.*`, `CryptoKernel`/`World`) — a step-complete
  running machine, `#eval`-able, with crypto-soundness kept on the Rust side of a clean §8 portal.

Honest calibration: dregg2 is **not** a finished verified distributed OS — it's a well-architected,
machine-checked, honestly-`sorry`-budgeted *seed* of one, growing module by module. `seL4`/`l4v`
is the north star (Abstract→Design→Refinement); we're early on that arc but the keystones are real.

## dregg1 — the running fabric (Rust)

A **unified fabric**: a shared blocklace (DAG) where groups form emergently through mutual
acknowledgment — no fixed federations. Your phone is a node; a cloud cluster is a node; the
sovereignty spectrum is continuous. Cells are isolated objects; turns are atomic state transitions;
CapTP sessions carry capability references; intents broadcast needs and ring trades solve them
trustlessly. (Semantic-core verification is dregg2's job; the algebraic/circuit debt is tracked in
`SILVER-DEBT.md`, *not* this README.)

### Key capabilities
- **CapTP** — sessions, sturdy refs, distributed GC, three-party handoff, store-and-forward.
- **Programmable Queues** — Merkle queues with attached DSL programs, enforced by the executor.
- **DFA Routing** — governance-controlled route tables compiled to prefix-trie state machines.
- **Nameservice** — hierarchical names, rent-based anti-squatting, cross-federation resolution.
- **Intent Solving** — privacy-preserving marketplace; commit-reveal; coordinator-free ring trades.
- **Effect VM** — an abstract instruction set proven per-turn in one STARK (hardening in progress).

### Quick start (dregg1)
```sh
git clone https://github.com/emberian/dregg && cd dregg
cargo build
cargo run -p dregg-node run                       # run a node
cargo run -p dregg-demo-agent                      # full pipeline: token + STARK + turn
cd docker && docker compose up                     # 4-node devnet
```

### Crate overview (dregg1)
| Crate | Purpose |
|-------|---------|
| `circuit` | STARK prover/verifier, Effect VM AIR, 17+ specialized AIRs, IVC, Plonky3 |
| `turn` | TurnExecutor: call forests, journal rollback, pipeline execution, queue programs |
| `cell` | Isolated objects with c-lists, notes, programs, oblivious transfer |
| `blocklace` | Shared DAG consensus. Content-addressed blocks, causal ordering, finality |
| `captp` | Capability Transport Protocol: sessions, sturdy refs, handoff, distributed GC |
| `federation` | Ed25519 BFT, state roots in blocks, epoch reconfig, LightClientProof |
| `intent` | Gossip broadcast, local Datalog matching, commit-reveal, IT-PIR discovery |
| `storage` | Programmable queues, relay operators, inboxes, erasure-coded availability |
| `bridge` | Token-to-circuit pipeline, blinded membership, predicate proofs |
| `cli` | User-facing CLI: cell, turn, cap, namespace, route, storage, cclerk |
| `sdk` | AgentCipherclerk, AgentRuntime, HD keys, verification modes, IT-PIR client |
| `node` | Federation daemon: HTTP API, MCP server, gossip sync |
| `net` | Quinn QUIC, Plumtree gossip, topic-based dissemination |
| `commit` | 4-ary Merkle trees (BLAKE3 fast / Poseidon2 ZK), fold deltas |
| `token` | AuthToken: Macaroon HMAC-SHA256 + Biscuit Ed25519+Datalog |
| `coord` | Causal DAG, 2PC atomic commit, Stingray bounded counters |
| `commit`/`store`/`wire`/`hints`/`wasm`/`dregg-dsl`/`verification`/`app-framework`/`apps/*` | merkle, persistence, framing, threshold sigs, WASM, the constraint DSL, the composition checker, and the app surface |

## Privacy model (the epistemic boundary, in practice)
Three verification modes from the same Datalog rules — the verifier's *epistemic position* is a dial:

| Mode | Verifier learns | Proof size |
|------|----------------|-----------|
| Trusted | Full cleartext + trace | 0 |
| Selective Disclosure | Chosen facts + conclusion | ~45 KB |
| Fully Private | One bit (allow/deny) | ~80 KB |

All modes work offline; proofs are post-quantum (BabyBear STARK + FRI). In dregg2's terms: each
mode is a different *epistemic boundary* over the same `Verify` seam.

## Links
- [Paper](https://dregg.dev/paper.html) · [Docs](https://dregg.dev/docs/) · [Playground](https://dregg.dev/playground/) · [Explorer](https://dregg.dev/explorer/)

## Status: experimental
Research software under active development. dregg1's proof system is real (Plonky3 STARKs,
algebraic Poseidon2, 2000+ tests); its networking/consensus are functional but not battle-tested.
dregg2 (the Lean verification) is early but its proved keystones are genuine and its `sorry`s are
honest. Do not use for anything security-critical without independent audit.

## License
MIT OR Apache-2.0
