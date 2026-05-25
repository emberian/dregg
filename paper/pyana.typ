// =============================================================================
// Pyana: A Distributed Object-Capability Runtime
// with Zero-Knowledge Authorization and Proof-Carrying State
// =============================================================================

#set document(
  title: "Pyana: A Distributed Object-Capability Runtime with Zero-Knowledge Authorization and Proof-Carrying State",
  author: ("Ember Arlynx"),
  date: datetime(year: 2026, month: 5, day: 24),
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
    Draft -- May 24, 2026 \
    `github.com/emberian/pyana`
  ]
]

#v(2em)

// --- Abstract ----------------------------------------------------------------

#heading(level: 1, numbering: none)[Abstract]

We present Pyana, a *proof-carrying capability mesh*: a distributed object-capability runtime in which sovereign cells---isolated agents owning their own state---communicate via atomic message turns, delegate authority through attenuated capability chains, and attest both authorization and state transition algebraically. The kernel is an OCapN-lineage Capability Transport Protocol (CapTP) for cross-vat invocation, an Effect VM that batches per-turn effects into a single STARK over a real BabyBear AIR, federated BFT consensus over a blocklace DAG with constant-size BLS threshold attestation, cross-cell algebraic binding via canonical bilateral identifiers, programmable predicates declaring per-cell invariants, trustless intent matching with real threshold decryption, and federation-bypass via direct sovereign-cell `peer_exchange` for partition-tolerant operation.

Cells are sovereign by default: the federation persists only a 32-byte state commitment per cell, never the cell's interior state. Authority is bearer-shaped (swiss numbers, handoff certificates) and faceted (EffectMask with monotonic narrowing); delegation is monotone (capability attenuation) and provable (the Capability Derivation Tree exists as proof structure, not kernel data structure). The runtime implements E-style distributed object semantics---promise pipelining via eventual references, three-party introduction, sealer/unsealer pairs for partition-tolerant offline transfer, and EROS-style factories for constrained cell creation with computable child verification keys.

The substrate carries algebraic teeth at every layer. Per-turn STARKs over a $tilde$151-column Effect VM AIR bind in-trace effects to a canonical turn hash, an effects-hash chain, an actor nonce, and a previous-receipt hash---giving algebraic answers to threats T1, T3, T5, T8, T11, and T15 of the executor-honesty audit. Per-cell proofs are joined into a single turn via shared public inputs (Stage 7-$gamma$.0); bilateral effects (`Transfer`, `GrantCapability`, `Introduce`) are joined across cells via canonical transfer/grant/intro identifiers $"transfer_id" = "Poseidon2"("domain" || "from" || "to" || "amount" || "ACTOR_NONCE")$ that any third party can recompute and cross-check (Stage 7-$gamma$.2 Phase 1, with the joint aggregation AIR designed as Phase 2). The federation type is unified: one canonical `Federation` subsumes the four prior disjoint concepts (`FederationCommittee`, `FederationMode`, opaque `federation_id`, the Morpheus simulator harness), with $"federation_id" = "BLAKE3"("committee_pubkeys" || "epoch")$ as a commitment to membership.

A predicate substrate generalizes macaroon-lineage caveats into a 21+ variant `StateConstraint` vocabulary (`WriteOnce`, `Monotonic`, `StrictMonotonic`, `AllowedTransitions`, `BoundDelta`, `AnyOf`, `TemporalPredicate`, `CapabilityUniqueness`, `RateLimitBySum`, ...) declared per-cell and evaluated by the executor as part of every state-modifying turn. Witness-attached predicates---those carrying a STARK or other proof against a commitment---unify under a single `WitnessedPredicate` shape with kind registry (`Dfa`, `Temporal`, `MerkleMembership`, `BlindedMembership`, `BridgePredicate`, `PedersenEquality`, `Custom { vk_hash }`) and three surface variants (`StateConstraint::Witnessed`, `Precondition::Witnessed`, `CapabilityCaveat::Witnessed`). A new authorization mode `Authorization::Custom { predicate, descriptor }` lets apps define multisig, DAO-quorum, time-locked, capability-conditional, or compute-attested authorization purely through the predicate registry, without kernel changes.

A constraint DSL compiles a single `CircuitDescriptor` into 8 code-generation backends (Rust evaluator, AIR constraints, Datalog rules, Kimchi gates, compile-time STARK, Midnight/ZKIR v3, native Plonky3, SP1 guest programs) with composition operators (`compose_and`, `compose_or`, `compose_chain`, `compose_aggregate`). Three production provers---a custom BabyBear/FRI STARK, Plonky3's `p3-uni-stark`, and Kimchi/Pickles over the Pasta curve cycle---offer write-once-prove-anywhere semantics. The Silver Vision (integration-complete, executor-trusted-but-coherent) is operational today; the Golden Vision (full algebraic-constraint folded DAG of attestations) is approached through a generalized `plonky3_recursion_impl` substrate (the recursive verifier AIR is being lifted from the `P3MerklePoseidon2Air` placeholder per Lane Golden-Edge Block 1) and through Kimchi/Pickles as a credible production-grade outer recursive layer.

Three new layers cap the substrate. Storage primitives---CapInbox, ProgrammableQueue, PubSubTopic, BlindedQueue, RelayOperator---are not new Effect variants but **cell-program patterns**: factory-declared compositions of slot caveats and bearer capabilities, enforced by the same executor loop as every other turn. DFA routing is a first-class userspace primitive (a `WitnessedPredicate { kind: Dfa }`) governing `RouteTarget::Userspace { kind, payload }` dispatch into governed namespaces, intent gossip topic filters, and CapTP pre/post filters. AppCipherclerk (a six-method handle) and EmbeddedExecutor + StarbridgeAppContext let apps run as pure userspace---no app-specific `Effect` variants, no `Authorization::Unchecked` placeholder turns, no $[0; 64]$ stub signatures.

Cross-chain bridges convert Pyana STARKs into native external-chain proofs: EVM (Level 2 via SP1/Groth16, $tilde$200K gas), Mina (Level 2, native Pasta curves), and Midnight/Cardano (Level 1.5 optimistic with dispute, Level 2 ZKIR v3 designed). Federation-bypass `peer_exchange` enables direct sovereign-cell-to-sovereign-cell signed state transitions with optional STARK `transition_proof`, partition-tolerantly carrying value across an offline interval before being promoted to federation order on reconnect.

The system is implemented in approximately 400k lines of Rust across $tilde$45 workspace crates, with thousands of tests, real STARK proof generation ($tilde$24 KiB proofs, sub-second generation on BabyBear4 extension field at 124-bit security), real Ed25519 and BLS12-381 cryptography, working multi-node QUIC consensus over a blocklace DAG, a browser extension cclerk, a full-citizen `pyana` CLI (cell/turn/cap/cipherclerk/federation/namespace/storage/directory/proof/route/register-federation/doctor), userspace apps via the AppCipherclerk pattern, a Discord bot, and a devnet deployment. Real Shamir-over-GF(256) + ChaCha20-Poly1305 threshold decryption (`federation::threshold_decrypt`) backs the trustless intent engine, wired into production via `node::state::trustless_intent_engine`---the prior cleartext `set_decrypted_intents` side-channel is replaced by real threshold combination.

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
