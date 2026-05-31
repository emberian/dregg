# PHASE — Proof-Carrying Without Recursive Compression

> **Provenance.** 2026-05-31, read-only design agent (Claude Opus 4.8, 1M).
> Scope: design the architecture in which dregg ships **a forest of standalone
> per-step proofs + the linking witness data**, and a verifier checks the tree
> *and that its proofs chain* — Proof-Carrying Data **minus** the accumulation
> step. Aggregation/recursion becomes a later performance optimization, not a
> correctness prerequisite.
> **No `.lean`/`.rs` file was edited. No build was run.** This doc is the only
> artifact.
>
> **Verdict in one line.** dregg already has every piece this needs and is
> *de-facto* doing it for single cells: per-step EffectVm proofs that bind
> `(OLD_COMMIT, NEW_COMMIT, EFFECTS_HASH, PREVIOUS_RECEIPT_HASH)` in their public
> inputs (`circuit/src/effect_vm/pi.rs:17–24,103`), a hash-pointer receipt chain
> verified by `turn/src/verify.rs:108–166`, and a block payload that *already*
> carries `signed_turn + receipt + Vec<witnessed_receipts>`
> (`blocklace/src/finality.rs:66–81`). The composition-soundness *glue* — that a
> tree of independent steps that chain `prev.new = next.old` is sound as a
> composite — is **already proved in Lean** for both the intra-cell case
> (`Exec/TurnForest.lean`) and the cross-cell case (`Exec/CrossCellForest.lean` +
> `Proof/ForestLTS.lean`). What is *missing* is one **explicit, named artifact and
> verifier** — a `ProofForest` — that packages the tree + the linking witness and
> a `verify_forest` that checks per-proof validity **and** the chain-link edges in
> one pass, with a Lean theorem of the exact shape
> `(∀ node. node sound) ∧ (∀ edge. prev.new = next.old) ⟹ composite sound`. The
> existing recursion code does **not** need to be on the critical path for this,
> and on honest inspection it is not a sound, useful aggregation today (§2).

---

## 0. The idea in one paragraph

A turn (or cross-cell turn-family, or whole call-forest) is a **DAG of steps**.
Today the temptation is: compress the DAG into one succinct recursive proof
(IVC / STARK-in-STARK / folding). dregg has **never** had a sound, working
version of that compression (§2). So we **don't compress**. We ship the *whole
forest* of per-step proofs, each standalone and independently verifiable, **plus
the linking witness data** an aggregate proof would have absorbed into its public
inputs. A verifier (a) verifies **every** proof in the forest against its own
public inputs, and (b) checks the **linking discipline**: each proof's
`NEW_COMMIT` equals the next proof's `OLD_COMMIT` along every happened-before
edge, and cross-cell edges balance (CG-5 `Σδ = 0`). Soundness of the composite is
then the conjunction of per-proof soundness (the §8/circuit cryptographic
assumption) and the linking check (a *combinatorial* fact, fully in Lean). Cost:
O(n) proof bytes and O(n) verify instead of O(1). Aggregation slots in **later**
as a pure performance swap that does not touch the soundness story.

---

## 1. What already exists per-step (the artifacts to package)

### 1.1 The per-action / per-step proof (the EffectVm AIR)

The granular proof unit is the **EffectVm AIR** over one cell-step. Its public
inputs (`circuit/src/effect_vm/pi.rs`) *already* expose exactly the linking
surface:

| PI field | const | meaning |
|---|---|---|
| `OLD_COMMIT` (4 felts) | `pi.rs:17–18` | input state commitment (Poseidon2, ~124-bit) |
| `NEW_COMMIT` (4 felts) | `pi.rs:20–21` | output state commitment |
| `EFFECTS_HASH` (4 felts) | `pi.rs:24–25` | the effects this step emitted |
| `TURN_HASH` / `EFFECTS_HASH_GLOBAL` | `pi.rs:86,92` | turn-identity + global effects (CG-2 binding surface) |
| `ACTOR_NONCE` | `pi.rs:99` | replay/sequence binding |
| `PREVIOUS_RECEIPT_HASH` (4 felts) | `pi.rs:103` | pins the proof to a receipt-chain position |
| `NET_DELTA_MAG/SIGN`, `INIT/FINAL_BAL` | `pi.rs:42–52` | the conservation surface (CG-5 half-edge) |
| `SOVEREIGN_WITNESS_SEQUENCE` | `pi.rs:204` | per-cell monotone counter (chain-walk replay protection) |

This is *the* point: **the commitments that make linking possible are already in
the proof's public inputs.** A proof says "I took a state committing to
`OLD_COMMIT` to a state committing to `NEW_COMMIT`, emitting `EFFECTS_HASH`, at
receipt-chain position `PREVIOUS_RECEIPT_HASH`." Per-action granularity (one proof
per call-forest action) was landed as task #76 (`W3-C`).

### 1.2 The receipt chain (the turn-level link)

`turn/src/verify.rs` already implements the link **at the receipt level**: a
`WitnessedReceipt` chain where receipt *i+1*'s `previous_receipt_hash` is the
BLAKE3 hash of receipt *i* (`verify.rs:108–166`; genesis has `None`,
`verify.rs:124`). `verify_chain` rejects any broken pointer
(`verify.rs:148,207`). This is the **ChainLink discipline at the artifact level**,
already coded and tested.

### 1.3 The witnessed-receipt artifact (the proof + the witness data)

`turn/src/witnessed_receipt.rs` wraps a `TurnReceipt` with the STARK proof bytes,
the public inputs, and (optionally) the **full trace witness** (`WitnessAvailability`,
`witnessed_receipt.rs:11–16`). This is the **"Silver Vision"** form
(`recursive_witness_bundle.rs:13–18`): *carry the full trace; the verifier
re-runs the AIR* — which is **precisely proof-carrying-data-minus-accumulation
for one step.** The `aggregate_membership` field (`witnessed_receipt.rs:48`) is a
*hook* for aggregation, always `None` in v1 — confirming the system was built
forest-first, aggregation-later.

### 1.4 The call-forest executor (the producer of the tree)

`turn/src/executor/execute_tree.rs` walks the **call-forest** (the nested
`Action` tree with delegated capabilities), producing one step per node. The
forest *shape* is the Rust mirror of the Lean `TurnForest` (§3). On the Lean side
`Exec/TurnForest.lean` proves the executor's tree-walk attests all four `StepInv`
conjuncts over the whole tree (§3.1 below).

### 1.5 The block payload (the forest already rides in the block)

`blocklace/src/finality.rs:66–81` — `TurnBlockPayload` carries
`signed_turn: Vec<u8>`, `receipt: Option<Vec<u8>>`, and
`witnessed_receipts: Vec<Vec<u8>>`. **The forest of proofs already travels inside
the consensus block.** No new wire shape is needed at the block layer; we need to
*name and verify* the forest as a unit (§5).

---

## 2. Honest assessment of the existing recursion/aggregation code

The owner's belief — *none of these is a sound, useful aggregation* — is
**substantially correct**. Detail, with file:line:

### 2.1 The "STARK aggregation via hash chain" (`plonky3_recursion.rs`)

`AggregationAir` (`plonky3_recursion.rs:42–55`) is a width-4 Poseidon2 **hash
chain** over the inner proofs' *public inputs*. Its own docstring is honest
(`plonky3_recursion.rs:20–26`):

> This is **NOT** full in-circuit recursion (verifying a STARK inside a STARK)…
> What we provide is proof aggregation: combining N proofs into 1 by proving
> knowledge of their public inputs in a hash chain. **The verifier still needs
> access to the inner proofs for full soundness**…

So the "aggregation proof" proves only *"these are the public inputs I hashed"* —
it does **not** prove the inner AIRs accepted. The inner proofs must still be
shipped and verified. **As an aggregation this is not useful** (it saves nothing —
you still carry and check every inner proof); as a *binding commitment to the
sequence* it is fine. This is, in effect, **already the proof-forest model with a
convenience digest** bolted on.

### 2.2 The "real recursion" path (`plonky3_recursion_impl.rs`, feature `recursion`)

There **is** a genuine in-circuit FRI verifier path: `FriRecursionBackend`,
`with_fri_opening_proof` (`:166`), `set_fri_mmcs_private_data` (`:208`),
`build_and_prove_next_layer` — wired to the upstream `p3-recursion` crate, gated
`#[cfg(feature = "recursion")]` and **in the default feature set**
(`circuit/Cargo.toml:78`). `plonky3_verifier_air.rs:1–25` claims this is "a
**real** recursive proof, not a placeholder."

Honest caveats that keep it off the critical path:

- It wraps `AggregationAir` (the hash chain of §2.1) as its inner AIR
  (`plonky3_verifier_air.rs:18–22`). So the outer recursive proof attests *"the
  hash-chain AIR was satisfied"* — i.e. it recursively proves the **digest**, not
  that each fold/EffectVm AIR accepted. The smoke test even notes "**The
  hash-chain computation is NOT enforced**" in the shape test
  (`plonky3_recursion_impl.rs:533–535`).
- FRI parameters in this path are **toy**: `num_queries`/arity tuned for shape,
  `query_proof_of_work_bits: 0` (`:256`), `2 queries` (`:237`) — soundness-margin
  parameters for a *demonstration*, not production security.
- The first (and primary) AIR proven through it is the 358-column
  `P3MerklePoseidon2Air` (`:17–19`), not the EffectVm AIR. Wrapping the *real*
  EffectVm AIR through it (so the outer proof attests the *transition*, not a
  Merkle/hash shape) is unproven-by-test on the critical path.

### 2.3 IVC (`ivc.rs`) and fold/bilateral aggregation

`ivc.rs:30–40` is explicit: *"Without the real recursion backend, the IVC is
implemented as a **HASH CHAIN** with constraint checking."* It checks fold
constraints **per step** and then extends a Poseidon2 accumulator — again, the
accumulator is a *digest of the sequence*, not a succinct proof that replaces the
per-step proofs. `bilateral_aggregation_air.rs` (γ.2) is the most real of the
batch: it lifts each inner proof's 74-PI vector into outer trace columns and
enforces CG-2/CG-3/CG-4 algebraically in one pass — but **CG-5 cross-side
existence is enforced *outside* the AIR by the prover's schedule construction**
(`bilateral_aggregation_air.rs:31–43`), and the in-circuit inner-proof
verification (CG-1) rides the same `plonky3_recursion_impl` substrate of §2.2.

### 2.4 Was there a refactor toward "generally proof-carrying"?

**Yes, structurally, and it is the right one.** The "Silver Vision"
(`recursive_witness_bundle.rs:13–18`, `witnessed_receipt.rs`) *is* carry-the-
trace-and-re-run-the-AIR. The "Golden Vision" (recursive proof) is the *optional*
swap, behind a `WitnessAvailability` enum and an always-`None` `aggregate_membership`
hook. The `ProofTier` enum (`proof_tier.rs:28`) marks the custom STARK and native
Kimchi as `Experimental` and is **informational only, not used for verification
acceptance** (`proof_tier.rs:13`). Kimchi/mina has 22 failing tests quarantined
(task #97).

### 2.5 Verdict on the recursion code

**Treat the recursion/aggregation modules as not-on-the-critical-path.** They are
either (a) hash-chain *digests* of a sequence whose inner proofs you must still
carry and check (`plonky3_recursion.rs`, `ivc.rs`) — i.e. the proof-forest model
with a commitment bolted on; or (b) a real-but-toy-parameterized FRI-in-circuit
path that today proves the *digest AIR*, not the EffectVm transition
(`plonky3_recursion_impl.rs`). None is a sound, useful *compression* that lets you
drop the per-step proofs. **The proof-forest architecture below depends on none of
them**, and is exactly what frees dregg to ship on the post-quantum STARK *now*
without needing STARK recursion to work.

---

## 3. The linking discipline (what must be checked to make a forest sound)

A `ProofForest` is sound as a composite iff three families of obligation hold.
This is the precise spec, mapped to the existing Lean.

**Per-proof (the leaf obligation).** Every proof `πᵢ` verifies against its public
inputs `PIᵢ = (oldᵢ, newᵢ, effectsᵢ, prevReceiptᵢ, δᵢ, …)` under the EffectVm AIR.
This is the cryptographic soundness assumption (the §8 circuit seam): a valid
`πᵢ` ⟹ there existed a witness driving `oldᵢ ⟶ newᵢ` emitting `effectsᵢ` while
satisfying the AIR's constraints (authority gate, conservation half-edge, etc.).

**Intra-cell chain-link (the sequential edge).** For consecutive steps on the
**same** cell along a happened-before edge `i ⟶ j`:
```
    new_commit(πᵢ)  =  old_commit(πⱼ)            (state continuity)
    prev_receipt_hash(πⱼ)  =  H(receiptᵢ)        (receipt-chain pointer)
    sovereign_sequence(πⱼ)  =  sovereign_sequence(πᵢ) + 1   (no replay/fork)
```
The state-continuity edge is the executable shadow of the Lean **ChainLink**
conjunct (`Exec/StepComplete.lean:54`, the new state's chain extends the old by
exactly this turn; the multi-action lift `Exec/TurnExecutor.lean:239`
`chainLink` — *"a committed turn extends the receipt chain by exactly its
moves"*). The receipt-hash edge is already coded in `turn/src/verify.rs:148,207`.

**Cross-cell balance-link (the family edge).** For a delegation/message edge that
crosses cells, there is **no global ledger**, so no single commitment continues.
The link is instead the **CG-5 N-ary conservation binding**: the signed
half-edges of the cross-cell family must satisfy `Σ_node δ = 0`, *and* every node
commits to the same shared turn-identity (CG-2: `TURN_HASH` /
`EFFECTS_HASH_GLOBAL` / `ACTOR_NONCE` / `PREVIOUS_RECEIPT_HASH` agree across the
family — exactly the bilateral aggregation's CG-2 group,
`bilateral_aggregation_air.rs:19–24`). This is the Lean `ForestTurn` Σ=0 binding
(`Proof/ForestLTS.lean:259` `forestApply_cg5_conserves`, carried as an explicit
hypothesis `hbind : ∑ i, ft.δ i = 0`, *never derived*).

**Granovetter (the authority edge, structural).** Every delegation edge confers
≤ the parent's authority (`derive_no_amplify`). This holds of *every* well-formed
forest, committed or not — it is a structural fact about the forest data, not a
runtime check (Lean `execForest_no_amplify`, `Exec/TurnForest.lean:238`;
`crossForest_no_amplify`, `Exec/CrossCellForest.lean:217`). The Rust gap here is
known and separate (CapTP `validate_handoff` assumes rather than enforces
non-amplification — task #94, `PHASE-DISTRIBUTED-CONFORMANCE.md` C1).

### 3.1 What the existing Lean already proves about composition

This is the load-bearing finding: **the composition side is already done.**

| Lean theorem | file:line | what it gives the forest |
|---|---|---|
| `execTurn_append` | `TurnForest.lean:142` | running a concatenated turn = running prefix then suffix (the fold associativity the flattening rests on) |
| `execForest_eq_execTurn` | `TurnForest.lean:173` | the tree transaction **equals** the linear transaction over its pre-order flattening — the bridge that lifts *every* `execTurn` theorem to the forest |
| `execForest_attests` | `TurnForest.lean:290` | a committed intra-cell forest attests all four `StepInv` conjuncts (Conservation ∧ Authority ∧ **ChainLink** ∧ ObsAdvance) over the **whole tree** |
| `execForest_conserves` | `TurnForest.lean:257` | `recTotal` preserved end-to-end (intra-cell CG-5, *derived* because every node is a balance turn on one cell) |
| `execForest_no_amplify` | `TurnForest.lean:238` | every delegation edge non-amplifying (Granovetter across the forest) |
| `forestApply_cg5_conserves` | `ForestLTS.lean:259` | **N-ary cross-cell CG-5**: joint family Σ-total preserved **given** `Σδ=0` (binding load-bearing, never derived) |
| `forestAbsStep_forward` | `ForestLTS.lean:306` | the N-ary cross-cell **forward-simulation square**: every committed family step under `Σδ=0` is matched by the abstract LTS edge (C5 + per-cell A + per-cell G) |
| `forestAbsRun_forward` | `ForestLTS.lean:377` | the square is **stable under iteration** over whole forest histories |
| `crossForest_attests` | `CrossCellForest.lean:278` | the four `StepInv` conjuncts over the whole **cross-cell** tree, binding-carried |
| `crossForest_needs_binding` | `CrossCellForest.lean:319` | the Σ=0 binding is a **genuine** restriction (a δ-family summing to 3≠0 is excluded) — proves the cross-cell forest cannot derive its conservation |

**Reading:** the abstract claim *"a forest of per-step transitions that (a) each
attest `StepInv` and (b) chain `new=old` / balance `Σδ=0` is sound as a
composite"* is **already a Lean theorem**, in both the intra-cell (chain-link,
derived) and cross-cell (Σ=0 binding, hypothesized) directions, including its
closure under iteration. The proof-carrying architecture is the *deployment shape*
of these theorems: it takes the thing Lean proves about the *executable model*
and realizes it over *cryptographic proof artifacts*.

---

## 4. The architecture: the proof-forest artifact + verifier

### 4.1 The artifact

```
ProofForest {
    nodes:  Vec<ForestNode>,          // one per step (pre-order, the call-forest)
    edges:  Vec<LinkEdge>,            // the happened-before DAG edges
    family_bindings: Vec<CrossFamily> // CG-5 groups (cross-cell turn families)
}

ForestNode {
    proof:        ProofBytes,         // standalone EffectVm STARK proof
    public_inputs: Vec<Felt>,         // the PI vector (OLD_COMMIT … HAS_TRANSITION_PROOF)
    witness:      WitnessAvailability // Silver: full trace; Golden(later): None
}

LinkEdge {
    kind: Sequential | CrossCell,
    from: NodeIdx, to: NodeIdx,
    // Sequential carries no extra data: the link is PI-equality (new=old, prev_receipt).
    // CrossCell points into a family_binding.
}

CrossFamily {                          // a CG-5 N-ary group
    members:    Vec<NodeIdx>,
    shared_turn_id: Felt4,             // CG-2 apex (TURN_HASH / EFFECTS_HASH_GLOBAL)
}
```

This is **almost entirely already present**: `ForestNode` = `WitnessedReceipt`
(`witnessed_receipt.rs`), the `edges` are recoverable from the receipt-chain
pointers + the call-forest structure `execute_tree.rs` already walks, and the
block already carries `Vec<witnessed_receipts>` (`finality.rs:77`). The *new* part
is making the `edges`/`family_bindings` **explicit and verifier-checked** rather
than implicit in chain order.

### 4.2 The verification algorithm (`verify_forest`)

```
verify_forest(F: ProofForest) -> bool:
  # (1) per-proof soundness — the cryptographic leaf obligation
  for node in F.nodes:
      require verify_effect_vm(node.proof, node.public_inputs)   # the §8 seam

  # (2) intra-cell chain-link — combinatorial, no crypto
  for e in F.edges where e.kind == Sequential:
      require PI(e.to).OLD_COMMIT      == PI(e.from).NEW_COMMIT
      require PI(e.to).PREVIOUS_RECEIPT_HASH == H(receipt(e.from))
      require PI(e.to).SOVEREIGN_SEQUENCE    == PI(e.from).SOVEREIGN_SEQUENCE + 1

  # (3) cross-cell balance-link — combinatorial
  for fam in F.family_bindings:
      require Σ_{n ∈ fam.members} signed_delta(PI(n)) == 0       # CG-5
      for n in fam.members:
          require PI(n).TURN_HASH            == fam.shared_turn_id  # CG-2
          require PI(n).EFFECTS_HASH_GLOBAL  == fam.global_effects

  # (4) well-formedness — the DAG is acyclic & roots link to attested prior state
  require acyclic(F.edges)
  require every root's OLD_COMMIT is the federation's last-attested commitment
  return true
```

Steps (2)–(4) are **pure combinatorics over felt vectors** — no proving, no
crypto beyond the BLAKE3 receipt hash. Step (1) is N independent
`verify_effect_vm` calls. The whole thing is `O(n)` and embarrassingly parallel.

### 4.3 Backend-agnosticism

The verifier reads only `OLD_COMMIT`/`NEW_COMMIT`/`EFFECTS_HASH`/… from the PI
vector and calls a backend `verify`. So the **same** `verify_forest` works with:

- **STARK now** (Plonky3 EffectVm AIR, `ProofTier::Production` for the poseidon
  STARK path, `proof_tier.rs:162`) — *no recursion required*;
- **Pickles/Mina later** (when the kimchi path is un-quarantined, task #97);
- **folding/IVC later** — by swapping a *node's* `proof` for a recursive proof
  over a *sub-forest*, with the linking edges that the sub-forest's boundary
  exposed. Crucially this is a **node-local** swap: the forest verifier is
  unchanged; only that node's `verify` becomes "verify the recursive proof,"
  and the edges into/out of the collapsed sub-forest are checked against the
  recursive proof's *boundary* public inputs (still `OLD_COMMIT`/`NEW_COMMIT`).

---

## 5. Soundness argument

**Theorem (shape).** Let `F` be a proof-forest with nodes `{πᵢ}`, sequential
edges `E_seq`, and cross-cell families `{Fₖ}`. If

- **(P)** for every node, `verify_effect_vm(πᵢ, PIᵢ) = true`
  ⟹ (by the EffectVm AIR soundness assumption, the §8 circuit seam) there is a
  witnessed step `sᵢ ⟶ sᵢ'` with `commit(sᵢ)=oldᵢ`, `commit(sᵢ')=newᵢ`,
  emitting `effectsᵢ`, satisfying the per-step `StepInv` (authority + the
  conservation half-edge);
- **(L_seq)** for every `(i⟶j) ∈ E_seq`: `newᵢ = oldⱼ` ∧ `prevReceiptⱼ = H(rᵢ)` ∧
  `seqⱼ = seqᵢ+1`;
- **(L_×)** for every family `Fₖ`: `Σ_{i∈Fₖ} δᵢ = 0` ∧ all members share the CG-2
  turn-identity;

then the forest denotes a single well-formed composite execution whose composite
`StepInv` holds: conservation across the whole DAG (intra-cell continuity +
cross-cell Σ=0), authority at every node, and a single consistent
happened-before chain (no fork/replay).

**Proof obligation split.**

```
composite_sound  ⟸  (∀ node. per_proof_sound)        # (P): cryptographic, the §8 seam
                  ∧  (∀ seq-edge. new = old ∧ receipt-link)  # (L_seq): combinatorial
                  ∧  (∀ family. Σδ = 0 ∧ CG-2 agree)         # (L_×): combinatorial
```

The right-hand conjuncts (L_seq), (L_×) — **the part dregg2 already models** — are
discharged in Lean *today*:

- (L_seq) and the resulting whole-tree `StepInv` are `execForest_attests`
  (`TurnForest.lean:290`) via the flattening bridge `execForest_eq_execTurn`
  (`:173`). The ChainLink conjunct is exactly `new = old` continuity over the
  pre-order fold (`TurnExecutor.lean:239`).
- (L_×) and the whole-family conservation + forward simulation are
  `forestApply_cg5_conserves` (`ForestLTS.lean:259`) and `forestAbsStep_forward`
  (`ForestLTS.lean:306`), with `crossForest_attests` (`CrossCellForest.lean:278`)
  giving the four conjuncts over the cross-cell tree, and `forestAbsRun_forward`
  (`ForestLTS.lean:377`) closing it under iteration.

So the composite-soundness theorem factors as **(cryptographic per-proof
soundness) × (the linking facts dregg2 has already proved combinatorially)**.

### 5.1 What is NEW (the gap to close)

The Lean theorems above are about the **executable model** (`execForest`,
`forestApply` over `KernelState`). The proof-forest deploys them over
**cryptographic artifacts** (STARK proofs over commitments). The missing bridge
is a small, honest module — call it `Exec/ProofForest.lean` — that:

1. Defines `ProofForest` as a tree of `(oldCommit, newCommit, effectsHash, δ,
   prevReceipt, seq)` records (the *public-input projection* of a node — no
   crypto inside Lean);
2. Defines `linkOk : ProofForest → Bool` = the §4.2 (2)–(4) combinatorial check;
3. Proves `proofForest_composes`:
   `linkOk F = true → (∀ node ∈ F, perStepInv node) → fullForestInv (rootState F) F (leafState F)`
   — i.e. *"if the links check **and** every node's PI-projection satisfies the
   per-step invariant the AIR is **assumed** (§8) to attest, the composite
   satisfies the whole-forest `StepInv`."* This reuses `execForest_attests` /
   `crossForest_attests` directly — it is a re-statement of them with the
   per-node hypothesis named as "the AIR attested this PI," not new mathematics.
4. The `perStepInv node` premise is the **declared cryptographic assumption** (the
   §8 circuit seam), entered as a hypothesis, *exactly* as `CryptoKernel`/`World`
   portals enter their assumptions — never an `axiom`/`sorry` inside the proof.

This is a **half-day Lean module**, not research: it names the §8 assumption per
node and applies an existing theorem. The *Rust* side is `verify_forest` (§4.2)
plus a differential test that `verify_forest` accepts iff the Lean `linkOk`
accepts on the same PI vectors (the FFI golden-oracle cascade, the dregg2 house
style).

---

## 6. Cost / privacy table

| dimension | proof-forest (this design) | aggregated (later) | note |
|---|---|---|---|
| **proof bytes on wire** | O(n) — every per-step proof | O(1) — one succinct proof | n = #steps in the turn/forest |
| **verify time** | O(n), parallel | O(1) (+ one recursive verify) | forest verify is embarrassingly parallel |
| **prover time** | O(n) (n independent proofs) | O(n) + recursion overhead (seconds/layer) | aggregation is *more* prover work up front |
| **linking witness on wire** | the PI vectors (commitments, effects-hash, δ, seq) per node | absorbed into the recursive proof's PIs | this is the "data an aggregate would have hidden" |
| **storage** | full forest (Silver: + traces) | one proof + boundary PIs | Silver traces are hundreds of KB/step (`recursive_witness_bundle.rs:14`) |
| **interaction-graph privacy** | **LEAKS the DAG shape** (see §6.1) | hides intermediate structure | the central privacy cost |

### 6.1 The privacy implication (honest)

Shipping the forest **reveals the interaction graph**: a verifier sees *how many*
steps, the per-step commitments, the effects-hashes, the δ-magnitudes, and the
edge structure (who-linked-to-whom). An aggregated proof would have *hidden* all
intermediate commitments and edges behind one succinct statement. **This is a real
cost, not a wash.** Mitigations available without aggregation:

- The per-step commitments are already **hiding** (Poseidon2 of state, ~124-bit,
  `pi.rs:16`); the *values* are not on the wire, only commitments + δ.
- δ-magnitudes can ride as Pedersen commitments with the Σ=0 check done in the
  exponent (the hidden-asset equality argument already exists, task #84) — so the
  CG-5 link is checkable **without** revealing individual δ. This recovers
  amount-privacy while still shipping the forest.
- The DAG *shape* (fan-out, depth) remains visible. Hiding *that* genuinely needs
  aggregation (or onion-style per-edge blinding) — and is the honest reason
  aggregation is a *desirable* later optimization, **not** a correctness one. It
  buys **graph-topology privacy** and **O(1) bandwidth**, nothing in the soundness
  column.

Note the existing zero-knowledge STARK (trace blinding, task #74) already keeps
the *witness* hidden per step; the forest leak is specifically the **graph**, not
the witnesses.

---

## 7. Consensus integration (Cordial Miners / blocklace)

The forest rides **inside the block payload** — it already does:
`TurnBlockPayload { signed_turn, receipt, witnessed_receipts }`
(`finality.rs:66–81`). Key alignment with `study-consensus.md`:

- **Consensus = canonicity, orthogonal to proof/validity** (`study-consensus.md:20,226`).
  A proof attests *"this is **a** valid history"*; it provably **cannot** say
  *"this is **the** canonical next history"* — two equivocating valid turns each
  carry a perfect validity proof, and the proof system is symmetric in them
  (`study-consensus.md:46–50`). **The proof-forest is purely the validity layer.**
  It makes no claim about ordering; Cordial Miners' blocklace decides *which*
  forest is canonical (the τ-order debit rule, `study-consensus.md:135`).
- So the forest verifier runs **per block** as the validity gate: a block is
  *valid* iff `verify_forest(payload.proof_forest)` accepts and its root links to
  the cell's last-attested commitment (§4.2 step 4). Canonicity (which valid block
  wins a fork) is the **separate** blocklace finality machinery
  (`finality.rs::FinalityTracker`, quorum at 2f+1, `PHASE-DISTRIBUTED-CONFORMANCE.md`
  B5).
- This is *why* the forest model fits consensus cleanly: O(n) per-block validity
  is local and parallel, and the linking discipline (`new=old`, `Σδ=0`) is exactly
  the per-block invariant a miner re-checks on receipt — no global recursive proof
  to maintain across the DAG.

Aggregation, when it lands, changes only the *size* of `witnessed_receipts` in the
payload (one recursive proof + boundary PIs instead of n), not what consensus
does with it.

---

## 8. How aggregation slots in LATER (pure performance)

Because the verifier reads only the PI projection and calls a backend `verify`
(§4.3), aggregation is a **node-local artifact swap with an unchanged soundness
story**:

1. Pick a sub-forest `S ⊆ F` (e.g. one cell's run, or one turn-family).
2. Build a recursive proof `π_S` that attests *"every node in `S` verified **and**
   `S`'s internal links checked"* — i.e. `verify_forest(S)` as a circuit. The
   boundary PIs of `π_S` are `S`'s **frontier** commitments (the `OLD_COMMIT`s of
   `S`'s roots, the `NEW_COMMIT`s of `S`'s leaves) and `S`'s net δ.
3. Replace `S` in `F` by a single node carrying `π_S` and `S`'s frontier PIs.
4. `verify_forest` is **unchanged**: it verifies `π_S` (a backend `verify`) and
   checks the *frontier* links against the rest of `F` exactly as before.

The soundness theorem (§5) is *closed under this substitution*: replacing `S` by
`π_S` is sound iff `π_S` attests `verify_forest(S)`, which is the §5 theorem
applied to `S`. Lean-side, this is `forestAbsRun_forward` (`ForestLTS.lean:377`) —
the forward square is already proved **stable under iteration**, which is exactly
"a sub-run can be summarized by its endpoints." So aggregation **provably does not
change** the composite-soundness statement; it only shrinks bytes and (with
in-circuit verification) hides the sub-forest's internal graph. **The day STARK
recursion is sound and EffectVm-shaped, it drops in here with zero changes to the
forest verifier or the soundness proof.**

---

## 9. Smallest first verifiable increment

**A 2-step linked proof-forest, verified end-to-end on the real EffectVm AIR,
with the linking constraint checked.**

Concretely (mirrors the Lean `goodForest`, `TurnForest.lean:342`):

1. Produce **two real EffectVm STARK proofs** `π₀, π₁` for two consecutive
   single-cell steps (e.g. transfer 0→1 of 30, then 1→2 of 10), each via the
   existing `node/src/mcp.rs::generate_effect_vm_proof` → `WitnessedReceipt`
   pipeline (`witnessed_receipt.rs:21`). Constrain them so
   `NEW_COMMIT(π₀) = OLD_COMMIT(π₁)` and `prev_receipt(π₁) = H(receipt₀)`.
2. Package `ProofForest { nodes:[π₀,π₁], edges:[Sequential 0→1] }` (§4.1).
3. Implement the minimal `verify_forest` (§4.2 steps 1–2 only — no cross-cell yet):
   verify both proofs, then assert the two link equalities.
4. **Positive test:** `verify_forest` accepts. **Negative tests (the teeth):**
   (a) tamper `OLD_COMMIT(π₁)` so `≠ NEW_COMMIT(π₀)` → reject at the link check
   *even though both proofs individually verify*; (b) splice `π₁` from a different
   chain (wrong `prev_receipt`) → reject; (c) corrupt a proof byte → reject at
   step 1. (a) is the load-bearing one: it proves the **link** is what makes the
   composite sound, not the per-proof validity alone.
5. **Differential against Lean:** assert `verify_forest` accepts iff the Lean
   `linkOk` (§5.1) accepts on the same PI vectors — the FFI golden-oracle pattern
   already used for the kernel cascade (`Exec/FFI.lean`).

This increment uses **only the production Plonky3 EffectVm path — no recursion
feature, no aggregation** — and exercises the entire soundness story (per-proof ×
linking) at n=2. The cross-cell increment (a `Σδ=0` family, the `goodCrossForest`
shape `CrossCellForest.lean:408`) is the natural next step once the sequential
case is green.

---

## 10. Summary

- dregg is **already proof-carrying-minus-accumulation** for single cells: the
  EffectVm PIs carry `OLD/NEW_COMMIT` (`pi.rs:17–21`), the receipt chain links
  steps (`verify.rs`), the Silver witnessed-receipt carries proof+trace
  (`witnessed_receipt.rs`), and the block already ships `Vec<witnessed_receipts>`
  (`finality.rs:77`).
- The **composition soundness** — *linked forest of per-step proofs ⟹ sound
  composite* — is **already proved in Lean**, both intra-cell (`execForest_attests`,
  ChainLink-carried) and cross-cell (`forestAbsStep_forward` + `crossForest_attests`,
  Σ=0-binding-carried), and **closed under iteration** (`forestAbsRun_forward`).
- The existing recursion/aggregation code is **honestly not a sound, useful
  compression** today (§2): hash-chain digests that still require the inner proofs
  (`plonky3_recursion.rs`, `ivc.rs`), or a real-but-toy-parameterized FRI-in-circuit
  path that proves the *digest* AIR, not the EffectVm transition
  (`plonky3_recursion_impl.rs`). **Treat it as not-on-the-critical-path.**
- The missing work is small and named: one Lean module
  (`Exec/ProofForest.lean`) restating the existing composition theorems with the
  per-node §8 assumption named, and one Rust `verify_forest` + differential test.
  **The first increment is a 2-step linked forest on the real EffectVm AIR
  (§9), no recursion feature involved.**
- Aggregation slots in **later as a node-local artifact swap** that provably does
  not change the soundness statement (§8) — buying O(1) bandwidth and
  graph-topology privacy (§6.1), nothing in the soundness column. This is exactly
  what lets dregg ship on the post-quantum STARK **now**, carrying the tree
  instead of compressing it.

*OPEN (the residue beyond this design).* (1) Graph-topology privacy without
aggregation (onion/per-edge blinding) — genuinely wants the aggregation step or a
separate ZK construction. (2) The overlapping/contended forest (a cell incident to
two forests concurrently) — the coinductive `Boundary`, named OPEN in both
`ForestLTS §11` and `CrossCellForest §11`, off this critical path. (3) Wrapping the
**real EffectVm AIR** (not the digest AIR) through `plonky3_recursion_impl` with
production FRI parameters — the prerequisite for step (8) to be *useful*, not
merely *sound-by-substitution*.
