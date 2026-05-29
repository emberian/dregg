# gaps-1-substrate — the real dregg (Rust) vs the dregg2 design

> **Method:** surveyed the live workspace (`dregg-dsl/`, `circuit/`, `storage/`,
> `credentials/`, `cell/`, `turn/`, `bridge/`, `chain/`) against `dregg2.md` +
> `00-synthesis.md`. Tags per feature: **CAPTURED** (dregg2 explicitly absorbs it) ·
> **PARTIAL** (mentioned but reduced / one face of it) · **MISSING** (dregg2 is silent) ·
> **SUPERSEDED** (deliberately dropped/collapsed, with a stated successor).
>
> **Honest headline:** dregg2 is a *soundness-and-authority* rebuild. It is strong on the
> turn/cell/proof spine and deliberately collapses the proof-backend zoo. But three whole
> substrates the real code carries — **multi-target codegen + on-chain settlement**, the
> **storage substrate (blobs/queues/erasure/KZG)**, and the bulk of the **privacy
> cryptosystem** — are **largely uncaptured or only gestured at**. dregg2 must absorb them
> or explicitly declare them out-of-scope; right now they fall through the cracks silently.

---

## (a) DSL + 8 backends + on-chain verification

| Real feature | Status | Note | Where in dregg2 |
|---|---|---|---|
| `dregg-dsl` proc-macro frontend (`parse.rs`/`ir.rs`) | **PARTIAL** | dregg2 wants a Lean-first DSL via metaprogramming (§8, dec §9.1); the Rust proc-macro DSL is not mapped to it | §8 metatheory / "DSL via metaprogramming" |
| `gen_rust` evaluator | **CAPTURED** | = the trusted-cache eval; survives as the executor-as-cache | §1.2, §6 runtime |
| `gen_air` / `emit_stark_impl` (real, 788 LoC) | **CAPTURED** | folds into the one CCS/AIR statement | §7 (CCS IR) |
| `gen_kimchi` (250 LoC) | **SUPERSEDED** | Kimchi/Pickles demoted to interim recursion behind the trait | §7 ("~80%-built Pickles port behind the trait") |
| `gen_datalog` | **CAPTURED** | survives as the Datalog *engine* sibling of WitnessedPredicate | §3.1, §1.2 |
| `gen_midnight` (489 LoC, ZKIR v3) | **SUPERSEDED** | Midnight dropped as stale | §0(a) note in task; no successor doc |
| `gen_plonky3` (731 LoC) | **CAPTURED** | Plonky3/FRI is the chosen leaf | §7 (FRI/BabyBear leaf → WHIR) |
| `gen_sp1` (274 LoC) | **PARTIAL** | SP1-as-prover dropped, but SP1-as-**settlement-wrapper** (Groth16 for EVM) is a different role dregg2 never addresses | see settlement row |
| **Multi-target portability as a value** | **SUPERSEDED** | dregg2 picks ONE stack (FRI→WHIR, ProtoStar) + keeps CCS as the *only* portability hedge | §7 ("CCS as the one IR") |
| **On-chain settlement** (`chain/`: SP1→Groth16→EVM ~200k gas; `bridge/mina.rs`) | **MISSING** | dregg2 has NO settlement/anchoring story. Revocation root-epoch is the only "globalism seam" named. "EVM/SP1 settlement of a dregg2 proof across the network" is not designed | **gap** — belongs near §2.2 finality tiers / §3 revocation as a tier-0 anchor |
| `bridge/` cross-chain (mina, midnight observer, present) | **PARTIAL** | `bridge::present` is promoted to credentials (CAPTURED); the cross-chain *bridge/observer* role is dropped with Midnight, no replacement | §3 (token layer) for present only |

**The settlement story is the (a) headline gap:** dregg2's proof never leaves the dregg
network in the design. The real code can wrap a STARK into a Groth16 EVM proof — that *is*
"across the network" to a non-dregg verifier — and dregg2 is silent on it.

---

## (b) Proof / circuit stack vs PCA+IVC / CCS / folding-behind-a-trait

| Real feature | Status | Note | Where in dregg2 |
|---|---|---|---|
| ~21 hand-written AIRs (`circuit/src/*_air.rs`) | **PARTIAL** | dregg2 wants them all CCS-expressible; today they are bespoke Plonky3 AIRs, not CCS. Migration is assumed, not specified | §7 ("keep all AIRs CCS-expressible") |
| `effect_vm/` + `effect_vm_p3_air.rs` | **CAPTURED** | the in-circuit effect-fold = the §7.1 effect-fold conjunct | §7.1 (effect-fold) |
| `schnorr_air` / `native_signature_air` | **CAPTURED** | the auth-in-proof key→delegation conjunct | §7.1 (6-clause auth) |
| `ivc.rs` (FoldDelta/AccumulatedProof/IvcAir) | **SUPERSEDED** | replaced by ProtoStar folding behind `RecursionBackend` (no `additive_combine`) | §7 + build step 3 |
| Kimchi/Pickles recursion + `stark_in_pickles` | **PARTIAL** | kept only as interim impl behind the new trait | §7, build step 6 |
| `bilateral_aggregation_air` + `aggregate_bilateral_prover` (γ.2 cross-cell) | **PARTIAL** | dregg2 names "bounded-fan-in depth-1 aggregation" (the inner µI); cross-*cell* bilateral binding (equalizer/coequalizer, `ring_closure`) is NOT in the keystone type | §1.3 (inner µI) — but cross-cell binding under-specified |
| `proof_tier` enum (Production/Experimental/Structural) | **SUPERSEDED** | dregg2: tier is informational; acceptance is the crypto check. Aligns with "no experimental flags" memory | §7 (verify-not-tier) |
| `binius` / `garbled_air` backends | **MISSING** | neither mentioned; Binius (binary-field) and garbled-circuit AIRs simply vanish | **gap** — declare dropped or out-of-scope |
| Conservation in-proof | **CAPTURED** (as goal) | the "second rib" per-class CONSERVATION_VECTOR — but §9/build-step-1 admits it is likely NOT step-complete today | §6.1, §7.1 |

---

## (c) Storage substrate

| Real feature | Status | Note | Where in dregg2 |
|---|---|---|---|
| Content-addressed blobs (`content.rs`, `ContentHash`) | **PARTIAL** | dregg2 content-addresses *caps/CDT nodes & data-model values* (§1.1, §5), but the **blob store** as a substrate is not named | §5 (Preserves identity) — closest, but not the blob store |
| Blinded queues (`blinded.rs`, `dregg-storage-templates/blinded_queue`) | **MISSING** | no queue/inbox/mailbox primitive in dregg2 at all | **gap** |
| WAL (`wal.rs`) | **PARTIAL** | dregg2's "log is truth, DB is cache" (§6) is the *receipt chain*, not a storage WAL; relationship unstated | §2.4 / §6 (log-as-truth) |
| Reed-Solomon erasure coding (`erasure.rs`, XOR-prototype) | **MISSING** | data-availability / erasure is absent from dregg2 | **gap** |
| Sharding (`sharding.rs`) | **MISSING** | no horizontal-scale story | **gap** |
| KZG poly-queue (`poly_queue.rs`, real KZG10/BN254) | **MISSING** | a whole polynomial-commitment queue substrate (different curve from the FRI stack) is uncaptured | **gap** |
| pubsub / relay / inbox / quota / metering / multi_asset / namespace_mount | **MISSING** | the entire operator-economics + messaging layer is silent | **gap** |
| `dregg-storage-templates` (5 templates) | **PARTIAL** | only insofar as "sets → cells" (synthesis §5.2) could re-home some; the rest is uncaptured | §5.2 sets→cells (partial) |

**The (c) headline:** dregg2 effectively reduces storage to "sets-as-cells" + "identity =
hash of a data-model value." The **blob / blinded-queue / erasure / sharding / KZG-queue /
operator-economics** substrate — a large, partly-real body of code — is **uncaptured**.
dregg2 must say whether storage cells *are* these substrates or whether this is a separate
layer it inherits.

---

## (d) Privacy / anonymity

| Real feature | Status | Note | Where in dregg2 |
|---|---|---|---|
| Pedersen value commitments (`value_commitment.rs`, Ristretto) | **PARTIAL** | dregg2's value-rib is a Pedersen sum-to-zero chip *in the proof* (§6.1) — folds the homomorphic commit, but the standalone commitment type isn't mapped | §6.1 (value rib) |
| Bulletproofs range proofs | **PARTIAL** | §6.1 names "range" as part of the conservation chip; standalone Bulletproof path unmapped | §6.1 |
| Notes / nullifiers (`note.rs`, `nullifier_set.rs`) | **PARTIAL** | nullifier-uniqueness is dregg2's canonical tier-1 I-confluence example (§2.2); notes-as-private-state model itself not first-classed | §2.2 (nullifier example) |
| Stealth addresses (`stealth.rs`, EIP-5564-style) | **MISSING** | unlinkable per-tx CellIds — no analog in FieldVisibility/holder-blinding | **gap** |
| Sealing / sealer-unsealer (`seal.rs`, X25519+ChaCha20) | **CAPTURED** | = the caps↔keys ρ_in/ρ_out E-rights amplification at the membrane | §3 (ρ_in/ρ_out) |
| Shamir threshold | **MISSING** | threshold secret-sharing not in dregg2 | **gap** |
| Ring-blinding / ring closure (`ring_closure.rs`) | **PARTIAL** | coequalizer of N transfers; dregg2 cross-cell story is thin | §1.3 (cross-cell, under-spec) |
| Oblivious transfer (`oblivious_transfer.rs`, Chou-Orlandi) | **MISSING** | OT primitive uncaptured | **gap** |
| Selective disclosure / FieldVisibility | **CAPTURED** | dregg2 keeps FieldVisibility as attested endpoint property | §1, synthesis §5.1 |
| `credentials/` (issue/present/verify/revoke, unlinkable multi-show, BlindedMembership) | **CAPTURED** | = the biscuit/Obs-badge + revocation-as-non-membership | §3 (biscuit, revocation) |
| Anonymous/unlinkable delegation & invocation | **PARTIAL** | holder-blinding named; *invocation* unlinkability (per-turn) not designed | §3 |

**The (d) headline:** dregg2 captures sealing, selective disclosure, credentials, and folds
Pedersen/range into the value rib — but **stealth addresses, OT, Shamir threshold, and
per-invocation unlinkability** are genuinely **MISSING**. dregg2's privacy = FieldVisibility
+ value-rib + holder-blinding is a real *subset* of the deployed cryptosystem.

---

## (e) Lifecycle + factories

| Real feature | Status | Note | Where in dregg2 |
|---|---|---|---|
| `CellLifecycle` (Live/Sealed/Migrated/Destroyed/Archived) | **PARTIAL** | dregg2 keeps lifecycle as attested endpoint property + says checkpoint/restore/fork are codata theorems (§6); but **Sealed/Archived/Destroyed** as distinct states aren't mapped to the coalgebra | §1.3, §6 (runtime character) |
| Migrate / `migration.rs` | **PARTIAL** | synthesis §6.7 admits migration is a freeze-state-machine with no real transport; dregg2's target is "ship (id, head, rule) + receipts" | synthesis §6.7 (cleaner target named) |
| Seal/destroy as terminal objects | **CAPTURED** | CellLifecycle terminal objects kept (synthesis §5.1) | §1 |
| Factories (`factory.rs`, `CreateCellFromFactory`, ChildVkStrategy, CapTemplate, Provenance) | **MISSING** | the EROS constructor pattern — factory descriptor, child-VK derivation, approved-set, cap templates, provenance — is **not in dregg2 at all** | **gap** — belongs near §1.1 (minting an edge) + §5 (schema/AIR-id) |
| Archive (receipt-chain prefix archival) | **PARTIAL** | overlaps dregg2's log-is-truth / checkpoint, but prefix-archival-with-proof is unstated | §6 |
| Attested lifecycle transitions | **CAPTURED** (as intent) | "attested-lifecycle" is the dregg2 framing; just under-detailed per-state | §1.3 |

**The (e) headline: factories are MISSING.** The EROS/CreateFromFactory constructor —
arguably the load-bearing object-creation primitive — has no home in dregg2. Child-VK
derivation, cap templates, and provenance need to land at the §1.1 mint-an-edge / §5
schema-identity junction.

---

## TOP genuinely-missing / under-captured (the absorb list)

1. **On-chain settlement (`chain/` SP1→Groth16→EVM).** dregg2's proof never crosses to a
   non-dregg verifier in the design. This is real code and *is* "across the network."
2. **Factories / CreateFromFactory (the EROS constructor).** No home in dregg2 at all.
3. **The storage substrate** — blinded queues, erasure/DA, sharding, KZG poly-queue,
   operator-economics (quota/metering/relay/pubsub). Reduced to "sets-as-cells," leaving
   most of `storage/` + `dregg-storage-templates` uncaptured.
4. **Privacy primitives: stealth addresses, oblivious transfer, Shamir threshold,
   per-invocation unlinkability.** dregg2's privacy is a strict subset.
5. **Binius + garbled-circuit AIRs** vanish silently — declare dropped or out-of-scope.
6. **Cross-*cell* bilateral aggregation / ring-closure** (γ.2, equalizer/coequalizer) is
   not in the keystone `Cell = νC.µI…` type, which only models depth-1 *per-turn* fan-in.
