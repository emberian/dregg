# dregg1 → dregg2 — Migration & Strategy Plan

> **Status:** the concrete migration plan from **dregg1** (the existing ~60-crate Rust
> workspace) to **dregg2** (the Lean4 metatheory in `metatheory/` + the Lean⟷Rust
> *portal* `CryptoKernel`/`World`). Reads forward from `dregg2.md` (canonical
> architecture), `ROADMAP.md` (build sequence), `OPEN-PROBLEMS.md`, and the metatheory
> itself (`metatheory/Metatheory/{CryptoKernel,World,PrivacyKernel}.lean`,
> `Exec/{Kernel,Unified,FFI}.lean`).
>
> **The thesis.** dregg2 is not a rewrite of dregg1 in Lean. dregg2 is a *re-seating*:
> the **semantics** (what a turn means — conservation, authority/integrity, ordering,
> I-confluence, await/discharge, finality) move into verified Lean behind two portals,
> and the existing Rust becomes the **portal implementation** — the "rustful things"
> (crypto primitives, proving, transport, persistence, IDE/agent/bot/web). The contract
> between the two halves is the portal: `class CryptoKernel` (hash/verify/commit/
> nullifier + their laws) and `class World` (clock/recv/rand + monotonicity), plus the
> `@[export]`-compiled executable kernel (`Exec/FFI.lean`).
>
> **Two realizations of the portal, both real** (`CryptoKernel.lean` docstring): PROVING
> uses an abstract `[CryptoKernel …]` instance (uninterpreted symbols + laws — every Lean
> theorem is parametric, holds for any lawful impl); RUNNING uses Rust-supplied concrete
> types/impls via `@[extern]` / `@[export]`. So either side can be host. The cascade
> (§4) makes Rust the host and the compiled Lean the verified core.
>
> Tags: `[C]` grounded-in-code (`path`) · `[F]` forward-design · `[OPEN]` see
> OPEN-PROBLEMS.

---

## A. Crate-by-crate dregg1 → dregg2 mapping

Three fates (the prompt's (a)/(b)/(c)):

- **REPLACED-BY-LEAN** — the crate's *semantics* move into the metatheory; the crate
  either disappears or shrinks to a marshalling shim that calls the compiled Lean via
  the portal. (Its Rust is a v1 reference, frozen, not reshaped — per memory.)
- **STAY-RUST (portal impl)** — the "rustful things": crypto primitives, proving,
  transport, persistence, I/O, UI. These *implement* `CryptoKernel`/`World` or sit
  above the portal as transport/product. They do **not** move into Lean.
- **FFI-SHIM** — a thin Rust crate that hosts the compiled Lean (`@[export]` entry
  points) and marshals scalars/bytes across the C ABI; the dregg2-native home of
  the kernel.

| dregg1 crate | role today (`[C]`) | dregg2 fate | maps to (Lean module / portal) |
|---|---|---|---|
| `turn` (executor: authorize/execute_tree/finalize/apply) | call-forest turn model + `TurnExecutor` (`turn/src/executor/mod.rs:395`); auth runs as plain Rust (`executor/authorize.rs`) | **REPLACED-BY-LEAN** (semantics) | `Exec/Kernel.exec` + `Exec/Unified.step` (`KernelOp`); auth = `Exec/Caps` + `Authority/Positional.Integrity`; `Boundary.StepInv` is the step-complete statement |
| `cell` (program.rs, predicate.rs, state, lifecycle) | `CellProgram` + ~29 `StateConstraint`s (`cell/src/program.rs:53,597`); the coalgebra structure-map | **REPLACED-BY-LEAN** (semantics) + STAY for crypto carriers | `Exec/CellProgram.denote` (the structure-map); `Laws` (Predicate⊣Witness); carriers (`stealth.rs`, `value_commitment.rs`, `note.rs`) → `CryptoKernel`/`PrivacyKernel` |
| `coord` (atomic/causal/shared_budget) | two-layer coordination, non-pairwise overspend (`coord/shared_budget.rs`) | **REPLACED-BY-LEAN** | `JointTurn` (cross-cell ⊗, CG-2⊗CG-5), `Confluence` (non-pairwise escalation), `Finality.crossTierJoin` |
| `circuit` (AIRs, STARK, FRI, Plonky3, IVC, bilateral_aggregation_air) | the prover/verifier; `effect_vm/`, `schnorr_air`, `bilateral_aggregation_air` | **STAY-RUST (portal impl)** — discharges `CryptoKernel.verify`'s §8 obligation | implements `CryptoKernel.verify`/`hash`/`commit`; the binding/extractability is the circuit obligation, **never** a Lean law (`README §8`) |
| `credentials` (issue/present/verify/revoke; Dfa/Temporal/Bridge/Pedersen) | VC primitive over `bridge::present` STARK (`credentials/src/lib.rs`) | **STAY-RUST** (verifier impl) + Lean owns the *seam* | the verify/find seam = `Laws.Verifiable` instantiated by `CryptoKernel.verify`; predicate kinds (§3) become `CryptoKernel.verify` statements |
| `cell::predicate` (WitnessedPredicateRegistry, BlindedSet, dfa/temporal/merkle/pedersen) | the predicate registry + verifier plugins (`cell/src/predicate.rs:206`) | **REPLACED-BY-LEAN** (the seam) + STAY (the verifiers) | `Laws` (`Verify P w : Bool` decidable side / `find` opaque plugin); each `WitnessedPredicateKind` = a `CryptoKernel.verify` statement-type; `Privacy.BlindedSet` |
| `sdk` (cipherclerk, runtime, client, privacy, full_turn_proof) | client-local agent SDK + key/token/proof management (`sdk/src/lib.rs`, `cipherclerk.rs`) | **STAY-RUST** (portal impl + product) — see §B | `AgentCipherclerk` ≈ a held-`CryptoKernel`-instance + key store; turn *construction* stays Rust, turn *semantics* call compiled Lean |
| `wasm` (bindings/runtime/privacy) | browser playground over sdk primitives (`wasm/src/lib.rs`) | **STAY-RUST** (portal impl) | compiles the Rust portal impl (incl. real Bulletproofs) to wasm32; could also host wasm-compiled Lean later |
| `node` (mcp.rs ~46 tools, gossip, relay, consensus sync, api, ws) | the federation daemon + MCP agent surface (`node/src/mcp.rs`) | **STAY-RUST** (transport/product) hosting an FFI-SHIM kernel | the daemon is "above the core" (`dregg2 §10`); it *hosts* the verified `Exec` kernel via FFI; MCP tools = surface syntax over caps+await+badge |
| `blocklace` (finality, ordering, constitution, dissemination) | DAG-BFT consensus + τ-unified finality (`blocklace/src/finality.rs`) | **STAY-RUST** (impl) discharging `World` | implements `World.recv`/`clock`/`rand`; `Finality`/`World.committedByQuorum` is the Lean predicate it realizes; Byzantine safety/GST liveness `[OPEN]` |
| `net` (gossip, causal, node, message) | Plumtree gossip transport (`net/src/gossip.rs`) | **STAY-RUST** (transport) | below the portal; `dregg2 §10` "the core says *that* the CDT is gossiped, not *how*" |
| `captp` (gc, handoff, session, sturdy, pipeline, store_forward) | CapTP vat layer + distributed GC (`captp/src/gc.rs`) | **STAY-RUST** (impl) + Lean owns liveness law | `Liveness` (cyclic vs acyclic CDT, lease-expiry, `dead_undecidable`); REUSE the refcount half wholesale (`ROADMAP Phase 4`) |
| `token` (biscuit/macaroon backends, datalog_verify, revocation) | keys-as-caps token layer (`token/src/`) | **STAY-RUST** (crypto/format) + Lean owns the law | `Authority/Positional` (`ρ_in`/`ρ_out` lossy attenuation), `CryptoKernel.verify` for biscuit chains; `Laws` for datalog-as-search |
| `macaroon` (caveat, caveat_3p, discharge_gateway, crypto) | intra-vat HMAC caps + 3p caveats (`macaroon/src/`) | **STAY-RUST** (crypto) + Lean owns discharge | `Await` (discharge = the gateway resolver face); HMAC stays Rust |
| `intent` (matcher, solver, exchange, pir, sse, bond) | distributed intent engine (`intent/src/matcher.rs`) | **STAY-RUST** (untrusted solver) + Lean owns the seam | `Laws`/`Await` (intent = the ∃-resolver face; matcher = untrusted FIND plugin, `no_general_matcher`) |
| `dfa` (air, compiler, router, federation_verifier) | DFA routing engine (`dfa/src/`) | **STAY-RUST** (impl) + Lean owns the seam | a `WitnessedPredicateKind::Dfa` verifier → `CryptoKernel.verify` statement |
| `chain` (SP1→Groth16→EVM bridge) | on-chain settlement (`chain/`) | **STAY-RUST** (transport) | `dregg2 §10`: reaching a non-dregg verifier is a transport concern, not soundness |
| `storage` (blinded queue, templates) | storage substrate incl. blinded queue (`storage/src/blinded.rs`) | **STAY-RUST** (impl) + Lean owns privacy law | `Privacy`/`PrivacyKernel` (blinded queue = a set-cell, nullifier anti-double-spend) |
| `observability` (events, emitter, schema) | trace-event emitter for Studio (`observability/src/`) | **STAY-RUST** (I/O) | the runtime-character payoff (`dregg2 §6`) — checkpoint/replay are Lean *theorems*, the emitter is their I/O |
| `extension` (TS Chrome/Firefox + wasm) | browser cipherclerk extension (`extension/src/`) | **STAY-RUST/TS** (product) — see §B | the IDE/agent UI; the authenticated-workflow front-end = `Coordination`/`Projection` (MPST), `Protocol/Workflow` is its verified spine |
| `discord-bot` (cipherclerk, commands, flows) | Discord agent bot (`discord-bot/src/`) | **STAY-RUST** (product) | a product over the SDK; explicitly "rustful" per the prompt |
| `cli` (commands, output) | operator CLI (`cli/src/`) | **STAY-RUST** (product) | thin over SDK/node |
| `federation` | federation membership/state | **STAY-RUST** (impl) discharging `World` | membership bound is the protocol-supplied hypothesis `World` lacks (the `hbound` in `quorum_intersection_safety_OPEN`) |
| `app-framework`, `starbridge-apps/*`, `demo*` | product apps + server infra | **STAY-RUST** (product) | above the core; consume the SDK |
| `dregg-dsl*`, `dreggscript`, `dregg-dsl-differential` | caveat DSL + cross-backend differential harness | **STAY-RUST** as the **Lean↔Rust bridge** | `dregg-dsl-differential` is **backend #8**: Lean = golden oracle, empirical cross-validation over `sorry`'d regions (`ROADMAP`, `dregg2 §8`) |
| `verifier` | standalone Effect-VM proof verifier | **STAY-RUST** (TCB impl) | the minimal verifier = the §1.2 TCB; ideal first FFI-shim *consumer* of the compiled kernel |
| `preflight` | e2e promotion gate | **STAY-RUST** (CI) | the gate that runs the differential bridge |
| `types`, `commit`, `wire`, `persist`, `trace`, `secrets`, `hints`, `tokenizer`, `directory`, `rbg`, `bridge`, `discharge-gateway` | shared types, Merkle/commit, wire format, persistence, threshold sigs, directory/VFS, presentation bridge, HTTP gateway | **STAY-RUST** (plumbing/impl) | below or beside the portal; `secrets`/`commit`/`hints`/crypto = `CryptoKernel` material; `persist`/`wire` = transport; `directory`/`rbg` = userspace cells over the kernel |

**The shape of the table:** a *small* set of crates carry semantics and are
**REPLACED-BY-LEAN** (`turn`, `cell` program/predicate, `coord`) — these are the ones
the executable kernel (`Exec/`) and the law modules already model. A *large* set
**STAYS RUST** as portal implementation — every crypto, proving, transport, persistence,
and product crate. Exactly **one new kind of crate** is created: the **FFI-shim**
(today `Exec/FFI.lean`'s `@[export]` surface + its future Rust consumer, naturally
`verifier`/`node`).

---

## B. SDK / extension / cipherclerk impact

**The SDK split (the load-bearing change).** Today `dregg-sdk` does two jobs at once:
(1) **construction** — manage keys, attenuate tokens, build/sign turns, generate proofs
(client-local, `sdk/src/lib.rs` trust-model docstring); and (2) **semantics** — it also
*knows what a turn means* by virtue of building the structures the `TurnExecutor`
interprets. dregg2 cleaves these:

- **Construction STAYS RUST.** Key management, mnemonic/seed derivation, token
  attenuation (`HeldToken`/`DelegatedToken`), signing, witness-artifact assembly, the
  receipt-chain head (`ChainAppendError`/fork detection in `cipherclerk.rs:54`) — all
  remain the client-local Rust SDK. None of this is semantics; it is the agent's local
  cryptographic bookkeeping.
- **Semantics CALL THE PORTAL.** Where the SDK today *implies* turn meaning (what makes
  a turn admissible, conserving, integrity-respecting), it now calls the compiled-Lean
  kernel through the FFI-shim: "is this turn admissible / what is the post-state" is
  `Exec.exec`/`Exec.step` (`Exec/FFI.dregg_kernel_transfer_total`,
  `dregg_kernel_authorized`), not Rust logic the SDK and executor each re-implement.
  The differential harness (`dregg-dsl-differential`) keeps the Rust fast-path and the
  Lean oracle agreeing during the transition.

**What `cipherclerk` becomes.** `AgentCipherclerk` (`sdk/src/cipherclerk.rs:902`) is the
agent-side *crypto clerk* — Ed25519 identity, held tokens, receipt chain, proof
generation via the bridge. In dregg2 terms it is **a holder of a `CryptoKernel`
instance + a key store**, not a `CryptoKernel` itself. The distinction matters:

- The **`CryptoKernel` instance** (hash/verify/commit/nullifier + laws) is *one per
  process*, supplied by the crypto crates (`circuit`/`cell`/`secrets`/`commit`) — it is
  the portal impl. The cipherclerk *uses* it to commit, prove, and verify.
- The cipherclerk's own role — "holds keys, attests credentials, brokers capabilities"
  (its docstring) — is the **agent-as-principal** of `dregg2 §6b`: a holder of caps
  (biscuits / `CapabilityRef`s) identified by its key. That is product/identity, not
  crypto-interface. So: cipherclerk = `(key store) + (held caps/CDT view) + (receipt
  chain head)`, *parametric over* a `CryptoKernel`. The privacy methods on it
  (`stealth`, `private_transfer`, predicate proofs) become calls into
  `PrivacyKernel`-shaped operations realized over that portal instance.

**Extension / IDE-agent impact.** The extension (`extension/`) is the
authenticated-workflow / Coordination front-end (its README: page→content→background SW
holding keys + caps + receipt chain + ZK prover — a wasm cipherclerk in the browser).
In dregg2 the extension is unchanged in *kind* (STAY-RUST/TS product) but gains a
**verified backbone**: the workflow it drives (author→reviewer→CI, or any signer
choreography) is exactly `Metatheory/Protocol/Workflow.lean` — the RDII "DocuSign for
authenticated workflows" demonstrator, where `exec_authorized`/`exec_in_order`/
`merge_requires_approved`/`exec_attested`/`exec_appends` are **proved**. The extension's
"who may sign, in what order, with what attestation" is the choreography `G`
(`Coordination`/`Projection`) projected to a participant; the signature is a
`CryptoKernel.verify` (hence ZK-capable: attest authorization without revealing the
witness). So the extension's *guarantees* migrate into Lean while its *UI/transport*
stays exactly where it is. This is the differentiator the RDII memo names: the security
properties are machine-checked, not asserted.

**TS SDK (`sdk-ts`, `ts-sdk.archived`).** Same split: a thin TS client that talks to the
node (`extension/src/api.ts` is the pattern) and, where it needs semantics, hits node
endpoints that front the FFI-shim kernel. No TS reimplementation of semantics.

---

## C. Private predicates — the migration story

**Where dregg1 keeps predicates today.** Three overlapping places:
`cell::predicate::WitnessedPredicateRegistry` (the registry of verifier plugins:
`Dfa`/`Temporal`/`MerkleMembership`/`NonMembership`/`BlindedSet`/`BridgePredicate`/
`PedersenEquality`/`Custom` — `cell/src/predicate.rs:206`); `cell::program`'s
`AuthorizedSet`/`RenouncedSet` (`PublicRoot`/`BlindedSet`/`CredentialSet`,
`program.rs:309,316,338`); and `credentials` (the STARK presentation/predicate/
revocation proofs over `bridge::present`). The ~29 `StateConstraint` variants
(`program.rs:597`) compose these into the cell's admissibility filter.

**Where they go in dregg2.** The whole stack maps onto **two Lean seams plus the portal**:

1. **The verify/find seam = `Laws.Verifiable` (`Metatheory/Laws.lean`).** Every dregg1
   predicate is, abstractly, a `Verify P w : Bool` (decidable, verifier-local, in the
   TCB) paired with an *untrusted* `find : P → Option W` search plugin (no completeness,
   no termination). This is exactly the registry's structure: the registry holds
   verifiers (the `Verify` side, trusted), and the *prover* (DFA compiler, intent
   matcher, credential issuer) is the `find` side (untrusted). The migration **types**
   this honesty that dregg1 has only by convention: `Bool` (verify) vs `Option` (find).

2. **Each predicate *kind* = a `CryptoKernel.verify` statement-type
   (`Metatheory/CryptoKernel.lean`).** A `WitnessedPredicateKind` is a family of
   `(statement : Digest, proof : Proof)` pairs that `CryptoKernel.verify` adjudicates.
   `verifiableOfCryptoKernel` *is* the instance: `Verify stmt proof := CryptoKernel.verify
   stmt proof`. So `Dfa`/`Temporal`/`Merkle`/`NonMembership`/`Pedersen`/`Bridge` each
   become a `Digest`-shaped statement the kernel verifies; their **crypto soundness stays
   an interface obligation** the `circuit`/`credentials` Rust discharges (the §8 boundary
   — `discharged_iff_verify`).

3. **The private tiers = `Privacy`/`PrivacyKernel`.** `BlindedSet`/`CredentialSet`
   (Poseidon2 set-commitment membership, `program.rs:316,338`) is the **graph-privacy**
   tier (`Privacy.BlindedSet`, holder-blinded set membership); the value-commitment /
   nullifier predicates are the **value** and **nullifier** tiers, now *proved over the
   portal*: `PrivacyKernel.committed_conservation_kernel` (Pedersen opening of Law 1 over
   hidden amounts, PROVED via `commit_hom`) and `PrivacyKernel.nullifier_no_double_spend`
   (anti-double-spend from `nullifier` determinism). `FieldVisibility` selective
   disclosure is the cheapest **field** tier (`Privacy.project`). The algebra (homomorphism
   ⇒ conservation, determinism ⇒ no double-spend) becomes a *theorem* about any lawful
   kernel; hiding/unlinkability/extractability remain §8 circuit obligations.

**The migration sequence for predicates (concrete):**
- **Step 1 — type the seam.** Re-express the `WitnessedPredicateRegistry`'s contract as
  `Laws.Verifiable` + the `find`/`Verify` polarity. No code moves yet; this is the
  spec the Rust registry now refines.
- **Step 2 — route the built-in kinds through the portal.** For each of
  `Dfa`/`Temporal`/`Merkle`/`NonMembership`/`BlindedSet`/`Pedersen`/`Bridge`, fix the
  `Digest` statement-shape and confirm the Rust verifier is the `CryptoKernel.verify`
  for that shape. The differential harness asserts Rust-verify ≡ Lean-oracle on accept/
  reject (the dsl-differential backend #8 is built exactly for this).
- **Step 3 — the private tiers prove over `PrivacyKernel`.** Value/nullifier predicates
  inherit the PROVED `committed_conservation_kernel`/`nullifier_no_double_spend`; the
  Rust `value_commitment.rs`/`nullifier_set.rs`/`stealth.rs` become the portal impl.
- **Step 4 — `Custom`.** Stays the open extension point — a registered `find`/`Verify`
  pair the TCB checks, content-addressed by `ir_hash` (the `dregg2 §5` content-addressed
  structure-map). The DSL (`dregg-dsl`) is its untrusted compiler.

**The honest bound (`OPEN-PROBLEMS #4`):** ZK/private *choreographies* — proving
conformance to a projection `G ↾ p` without revealing `G` — is the cleanest fit for the
graph-privacy tier but is **confirmed-open** (MPST × ZK composition is not in the
corpus). So predicate privacy migrates cleanly *per-cell*; the *cross-party-private*
choreography is a research frontier, not a migration step.

---

## D. The cascade ORDER (phased plan; the portal interfaces are the contract)

The cascade FFI-routes the **thin verified kernel** first, then retires/rewrites dregg1
components against the Lean spec, always with the portal as the contract. This is
sequenced to keep dregg1 running the whole time (the differential harness is the safety
net), and to do the **soundness-critical audit first** (`ROADMAP Phase 0`).

**Cascade 0 — the FFI beachhead (DONE / in progress).** `Exec/FFI.lean` already
`@[export]`s the proved kernel: `dregg_kernel_transfer_total` and
`dregg_kernel_authorized` are the *same* `exec`/`authorizedB` whose `exec_conserves` /
`exec_authorized` are proved. **First Rust consumer = `verifier`** (the standalone TCB)
and a test harness in `dregg-dsl-differential`: link the compiled Lean, call the two
entry points, assert against the Rust executor. This proves the C-ABI seam end-to-end on
the smallest possible surface. *Contract:* the scalar marshalling (`UInt64 ⇄ ℤ`).

**Cascade 1 — instantiate the portals in Rust.** Provide the *real* `CryptoKernel`
instance from the crypto crates (`@[extern "dregg_poseidon_hash"]`, `…_verify`,
`…_commit`, `…_nullifier`) backed by `circuit`/`cell`/`commit`/`secrets`; provide the
real `World` instance (`@[extern "dregg_world_recv/clock/rand"]`) backed by
`blocklace`/`net`/`federation`. Now the compiled Lean, *running*, calls Rust for the
"actual semantics of actual things." *Contract:* `CryptoKernel`'s `commit_hom`/`hash_inj`
laws and `World`'s `recv_mono` law — the obligations the Rust impl must satisfy
(checked empirically by the differential harness; the binding/extractability is the
circuit's §8 obligation, never a Lean law).

**Cascade 2 — retire `turn`'s semantics into `Exec`.** The `TurnExecutor`'s
admissibility + authority + conservation decision (`execute_tree.rs`, `authorize.rs`)
is the dregg1 component most directly **REPLACED-BY-LEAN**. Route the executor's "is
this admissible / what's the post-state / is the actor authorized" through
`Exec.step` (`KernelOp` — transfer/mint/burn/grantCap/revokeCap). The Rust executor
becomes the *driver* (effect application, journaling, receipt-chain plumbing — the I/O)
around the verified decision core. Do this **after** Phase 0's step-completeness verdict,
because the in-circuit `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` is
what the Lean `Boundary` keystone requires and what dregg1 likely does *not* yet attest
(`ROADMAP Phase 0`: auth runs outside the proof today).

**Cascade 3 — the predicate seam (§C).** Re-type the predicate registry as
`Laws.Verifiable`, route built-in kinds through `CryptoKernel.verify`, and let the
private tiers prove over `PrivacyKernel`. The Rust verifiers stay; the *seam* is now
Lean-owned.

**Cascade 4 — `coord` → `JointTurn`/`Confluence`/`Finality`.** Cross-cell atomic turns
(the γ.2 bilateral aggregate, `coord`/`turn::aggregate_bilateral_prover`) re-seat onto
`JointTurn` (CG-2 ⊗ CG-5 binding-as-hypothesis) and `Confluence` (non-pairwise
escalation). **REUSE the circuit (`bilateral_aggregation_air`); the binding is a
Lean hypothesis, NEVER derived** (`ROADMAP Phase 3` inviolable rule). Finality
(`blocklace`) realizes `World.committedByQuorum`.

**Cascade 5 — the daemon hosts the kernel; products ride it.** `node` (and through it
the MCP surface, `extension`, `discord-bot`, `cli`, apps) hosts the FFI-shim kernel.
These STAY-RUST; they gain the verified core underneath but change little at the
surface. The runtime-character payoff (checkpoint/replay/time-travel, `observability`)
falls out as Lean *theorems* over the codata model (`Boundary`).

**Throughout:** the **metatheory track runs in parallel** (`ROADMAP`): close the
remaining `sorry`s (the genuine open theorems + the `World`/`CryptoKernel` interface
obligations the Rust+circuits discharge), keep `lake build` green, and keep the
differential harness asserting Rust ≡ Lean. **Never reimplement the prover in Lean;
never merge crypto-soundness into the law.**

Ordering rationale in one line: **audit step-completeness (Phase 0) → FFI beachhead →
portal instances → retire `turn` semantics → predicate seam → cross-cell → daemon/products**,
with crypto/proving/transport/UI staying Rust the entire time.

---

## E. Risks / open questions

1. **Step-completeness is unverified and probably false today (the gating risk).**
   `ROADMAP Phase 0` + memory: auth runs as plain Rust in `authorize.rs`, the PI surface
   lacks `AUTH_ROOT`/`ACTION_AUTHORITY_DIGEST`/`CONSERVATION_VECTOR`/
   `CONSTRAINT_MANIFEST_HASH`, and graph-folding is flat. Under coinduction a
   step-incomplete proof "permits a drifting future" — *nothing downstream is sound*.
   If the audit confirms this, Cascade 2 cannot land until step-completion is built
   (Phase 2), and the Lean `Boundary` keystone (`sound_of_step_complete`) stays an
   honest open. **This is the #1 risk and the reason Phase 0 gates everything.**

2. **Lean → C compilation + linking into a Rust crypto host is unproven at scale.**
   `Exec/FFI.lean` is a scalar-only PoC (`UInt64`); real turns carry `Digest`/`Proof`
   types and `Finset`-shaped state. Marshalling those across the C ABI, the Lean runtime
   (GC, `lean_object`) inside a Rust process, build-system integration (`lake` ⟷
   `cargo`), and wasm32 cross-compilation of compiled Lean are all open engineering. The
   scalar beachhead must generalize without the marshalling becoming its own unverified
   TCB.

3. **The portal laws are *assumed*, and the empirical bridge is not certification.**
   `commit_hom`/`hash_inj`/`recv_mono` are interface laws the Rust impl must satisfy but
   Lean never proves; the differential harness (backend #8) is *empirical cross-validation
   over `sorry`'d regions, not certification* (`dregg2 §8`). A Rust impl that violates a
   law (a non-homomorphic commit, a non-monotone receive log) makes the parametric Lean
   theorems vacuously inapplicable, silently. Mitigation: property-test the laws hard in
   the harness; keep the reference (Lean-as-host) kernels as the always-lawful baseline.

4. **Cross-disjoint-group atomic commit is a genuine impossibility, not a migration
   step (`OPEN-PROBLEMS #2`).** Safety is provable (CG-5 binding); liveness is not
   (2PC-blocks-under-partition; disjoint groups have no shared quorum). The cascade must
   not promise atomic-cross-group ∧ partition-tolerant ∧ live; `coord`/`cross_reference.rs`
   references peer-group blocks but cannot make them *agree*. Design around it (restrict
   to I-confluent ops, or accept blocking+timeout), do not "fix" it.

5. **The three-judgement projection split is dregg2's strongest *original* claim and is
   open (`OPEN-PROBLEMS #1`).** I-confluence is independent of conservation and ordering;
   the classifier is NOT the session type. The coordination layer (the choreography
   front-end driving the extension/workflow product) rests on a theorem no paper in the
   corpus supplies. Treat the `Coordination`/`Projection` modules' central soundness as
   research-grade; ship `JointTurn` (bilateral) first.

6. **dregg1 reality diverges from the dregg2 design in specific places (be honest):**
   - **Auth-in-proof does not exist** — the single biggest gap (risk #1).
   - **Distributed GC is acyclic-only** — `captp/src/gc.rs` does refcount drops; cyclic
     dead-cycle collection needs a mark-from-roots trace the runtime lacks. The Lean
     `Liveness` model says lease-expiry reclaims it; the runtime must actually implement
     leases (`gc.rs:14 TODO(unified-lace)`).
   - **`CallForest` copied Mina's tree but never built caller frames** — the
     `May_use_token` modes are dead (`ROADMAP Phase 1.3`); either flatten or build frames
     before the JointTurn cascade.
   - **The cipherclerk name is a known misnomer** (its own docstring): it manages
     capabilities, not balances; the dregg2 `agent-as-principal` framing fixes this.
   - **IVC recursion is deferred by impossibility** (`OPEN-PROBLEMS #5`): depth is a
     security parameter. The cascade must keep recursion behind `RecursionBackend` and
     off the soundness path.

7. **Naming/identity: the badge means permitted + effects-as-committed, NOT de-facto
   authority (`OPEN-PROBLEMS #6`).** A zkRPC/SDK product that sells a returned badge as
   "this principal can do X" overclaims — permission survives the crossing, authority
   does not. The SDK/extension product surface must be honest about what a badge attests.

---

## Appendix — the contract surface (the portal, in one place)

- **`CryptoKernel Digest Proof`** (`metatheory/Metatheory/CryptoKernel.lean`):
  `hash : List Nat → Digest`, `verify : Digest → Proof → Bool`,
  `commit : Int → Int → Digest`, `nullifier : Digest → Digest`; laws `commit_hom`,
  `hash_inj`. Instantiates `Laws.Verifiable` (`verifiableOfCryptoKernel`); closes the
  cross-vat integrity bridge (`cross_vat_via_verify`). Rust discharges via `@[extern]`.
- **`World Msg`** (`metatheory/Metatheory/World.lean`): `clock`, `recv`, `rand`; law
  `recv_mono`. Realizes `Finality.Committed` as `committedByQuorum`; `world_no_downgrade`
  PROVED; Byzantine safety / GST liveness `[OPEN]`. Rust (node runtime) discharges.
- **`Exec` kernel** (`Exec/{Kernel,Unified,FFI}.lean`): `KernelOp` + `step`;
  `exec_conserves`/`exec_authorized`/`step_delta`/`unified_ledger` PROVED;
  `@[export dregg_kernel_transfer_total]`/`dregg_kernel_authorized` = the cascade seam.
- **The bridge** (`dregg-dsl-differential`, backend #8): Lean = golden oracle; empirical
  Rust ≡ Lean cross-validation. **Not** certification.
