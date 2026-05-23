// =============================================================================
// Pyana: A Distributed Object-Capability Runtime
// with Zero-Knowledge Authorization and Proof-Carrying State
// =============================================================================

#set document(
  title: "Pyana: A Distributed Object-Capability Runtime with Zero-Knowledge Authorization and Proof-Carrying State",
  author: ("Ember Arlynx"),
  date: datetime(year: 2026, month: 5, day: 21),
)

#set page(
  paper: "us-letter",
  margin: (x: 1.2in, y: 1.2in),
  numbering: "1",
  header: context {
    if counter(page).get().first() > 1 [
      #set text(size: 9pt, fill: luma(100))
      Pyana: Distributed Object-Capability Runtime
      #h(1fr)
      Draft -- May 2026
    ]
  },
)

#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.58em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#show heading.where(level: 1): it => {
  v(1.2em)
  text(size: 14pt, weight: "bold", it)
  v(0.6em)
}
#show heading.where(level: 2): it => {
  v(0.8em)
  text(size: 12pt, weight: "bold", it)
  v(0.4em)
}
#show raw.where(block: true): set text(size: 9pt)
#show raw.where(block: true): block.with(
  fill: luma(245),
  inset: 8pt,
  radius: 3pt,
  width: 100%,
)

// --- Title -------------------------------------------------------------------

#align(center)[
  #text(size: 18pt, weight: "bold")[
    Pyana: A Distributed Object-Capability Runtime \
    with Zero-Knowledge Authorization and Proof-Carrying State
  ]
  #v(1em)
  #text(size: 11pt)[Ember Arlynx]
  #v(0.3em)
  #text(size: 10pt, fill: luma(80))[
    Draft -- May 23, 2026 \
    `github.com/emberian/pyana`
  ]
]

#v(2em)

// --- Abstract ----------------------------------------------------------------

#heading(level: 1, numbering: none)[Abstract]

We present Pyana, a distributed object-capability runtime in which sovereign cells---isolated agents owning their own state---communicate via atomic message turns, delegate authority through attenuated capability chains, and prove authorization in zero knowledge. The core observation is that monotonic capability attenuation---restricting a bearer token's scope through successive delegation---forms an incrementally verifiable computation: each restriction step is a fold over a committed fact set, producing a strictly smaller successor state. We encode capabilities as Datalog fact sets, commit them to 4-ary Merkle trees using Poseidon2 over BabyBear, and prove correct evaluation of authorization rules inside a STARK. The verifier learns a single bit---authorized or not---without observing the delegation chain, intermediate authorities, or the agent's other capabilities.

Cells are sovereign by default: the federation stores only a 32-byte state commitment per cell, not the cell's state. Cells interact peer-to-peer with STARK proofs, registering and deregistering from federation on demand. The runtime implements E-style distributed object semantics: promise pipelining via eventual references, three-party introduction for capability routing, sealer/unsealer pairs for partition-tolerant offline transfer, and EROS-style factories for constrained cell creation with auditable verification keys. Faceted capabilities (EffectMask with monotonic narrowing) and bearer capabilities (immediate grant without c-list storage) extend the E-semantics authorization model. A privacy-preserving intent marketplace enables capability discovery without leaking what agents hold. State is proof-carrying: receipt chains serve as the primary state representation, with IVC compression and federation reduced to an ordering service over nullifiers. A Capability Derivation Tree---the distributed dual of seL4's CDT---tracks delegation lineage as a proof structure rather than a kernel-enforced tree.

A constraint DSL compiles a single `CircuitDescriptor` into 8 code generation backends (Rust evaluator, AIR constraints, Datalog rules, Kimchi gates, compile-time STARK, Midnight/ZKIR v3, native Plonky3, and SP1 guest programs). Three production provers---a custom BabyBear/FRI STARK, Plonky3's p3-uni-stark, and Kimchi/Pickles over Pasta curves---enable write-once-prove-anywhere semantics with composition operators (`compose_and`, `compose_or`, `compose_chain`, `compose_aggregate`). STARK-in-Pickles wrapping produces constant-size recursive SNARKs; SP1 wrapping produces Groth16 proofs for EVM verification at ~200K gas. An Effect VM circuit proves arbitrary turns in a single STARK regardless of effect count.

The economic model provides sustainable federated validation without inflation: fees are split between proposer, treasury, and burn; validators stake via privacy-compatible range proofs; and an EIP-1559-adapted fee market adjusts to demand. An AI agent coordination substrate treats agents as first-class entities with identity, authority, economic relationships, and auditable histories---the networked analog of seL4's process isolation.

A Capability Transport Protocol (CapTP) extends Cap'n Proto RPC with sturdy refs, distributed GC, three-party handoff, store-and-forward via MerkleQueue inboxes, and 4 provable effects in the Effect VM. DFA-based governable routing with constitutional amendment provides namespace-level access control provable via STARK lookup tables. A service mesh (mount/discover/resolve) and petname-based nameservice (edge names, hierarchical resolution, sub-delegation, rental, dispute) build atop DFA routing. Storage economics (space banks, computron-metered storage, sender-pays-deposit anti-spam, erasure coding) and deep garbage collection (state lifecycle with birth/active/decay/forced sovereignty, storage rent, epoch rotation) sustain the system long-term. Cell migration (teleportation between federations, vat splitting/merging) with IVC proof continuity enables fluid trust boundaries. A typed composition checker with 30 verified circuit descriptors, 11 cryptographic guarantees, and 7 explicit trust assumptions provides formal verification foundations. Three bridges---EVM (Level 2 via SP1/Groth16, ~200K gas), Mina (Level 2, native Pasta curves, ~8 weeks), and Midnight (Level 1.5 optimistic+dispute)---connect to external chains via proof translation.

The system is implemented in approximately 355k lines of Rust across 41 workspace crates, with 4,046 tests, real STARK proof generation ($tilde$24 KiB proofs, sub-second generation on BabyBear4 extension field at 124-bit security), real Ed25519/BLS12-381 cryptography, working multi-node TCP consensus, a browser extension wallet, a full-citizen `pyana` CLI (cell/turn/cap/wallet/federation/namespace/storage/directory/proof/route/doctor), 8 production applications (gallery, stablecoin, AMM, orderbook, lending, identity, compute-exchange, bounty-board), a Discord bot, and a devnet deployment with 3 federation nodes.

#v(1em)

// --- Sections ----------------------------------------------------------------

#include "sections/01-introduction.typ"
#include "sections/02-model.typ"
#include "sections/03-authorization.typ"
#include "sections/04-proofs.typ"
#include "sections/05-privacy.typ"
#include "sections/06-fabric.typ"
#include "sections/07-captp.typ"
#include "sections/08-storage.typ"
#include "sections/09-service-mesh.typ"
#include "sections/10-intents.typ"
#include "sections/11-delegation.typ"
#include "sections/12-bridges.typ"
#include "sections/13-economics.typ"
#include "sections/14-agents.typ"
#include "sections/15-implementation.typ"
#include "sections/16-formal-verification.typ"
#include "sections/17-comparison.typ"
#include "sections/18-future.typ"
#include "sections/19-conclusion.typ"

// --- Appendices -------------------------------------------------------------

#include "sections/appendix-a-garbled-poseidon2.typ"

// --- References --------------------------------------------------------------

#heading(level: 1, numbering: none)[References]

#set text(size: 9.5pt)

#bibliography(title: none, style: "ieee", "refs.yml")
