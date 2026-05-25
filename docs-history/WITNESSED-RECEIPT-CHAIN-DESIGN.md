# Witnessed Receipt Chain — Design

Status: design exploration. Companion to `STAGE-7-GAMMA-AGGREGATION-DESIGN.md`
(cross-cell binding); this document covers the orthogonal *witness/replay*
dimension. Where the gamma doc says "two cells, one proof," this one says
"one cell, two epochs, replayable."

The user prompt that triggered this doc:

> Receipt chains should be sufficient to replay the protocol (with also the
> private inputs/witness data) to within a margin that is useful for
> constraining behavior in the future.

The phrasing matters. The user is not asking for universal third-party
replay. They are asking for *a sufficient artifact for someone we choose to
trust later*. That phrasing scopes everything that follows.

---

## 1. What "replay" means precisely

Today's `TurnReceipt` (`turn/src/turn.rs:263`) is a Merkle/hash bundle:
`turn_hash`, `forest_hash`, `pre_state_hash`, `post_state_hash`,
`effects_hash`, derivation records, emitted events, an optional executor
signature, plus chain-binding via `previous_receipt_hash`. Receipts hash
each other into a chain. Crucially, **a receipt does not embed the STARK
proof that justified its post-state.** The proof bytes live elsewhere
(custom-program proofs travel with the turn in
`turn.custom_program_proofs`, the Effect-VM proof is verified during
commit and discarded, sovereign cells' `execution_proof` lives on the
`Turn` itself but is not echoed back into the receipt). And nothing
carries the *witness* — the trace columns
(`generate_effect_vm_trace` returns `(Vec<Vec<BabyBear>>, Vec<BabyBear>)`,
i.e. trace + public inputs; the trace is most of the witness) and the
private secrets that feed it.

Four candidate replay scopes:

1. **Re-verify only.** Third party has the receipt chain plus the prover's
   STARK proofs (`StarkProof` bytes). They reconstruct each AIR by name,
   read the embedded public inputs, and run `stark::verify`. This is
   essentially the current `pyana-verifier` binary path, just generalized
   to a chain instead of a single proof. Catches malformed proofs and
   tampered public inputs (boundary commitment binds PI to trace cells).
   Does **not** catch a witness that produces the same proof for
   different private inputs (proof-of-knowledge soundness rules this out
   under STARK soundness, but the proof system's soundness is the only
   thing standing between you and a forged witness — there is no second
   check).
2. **Re-derive trace + verify.** Third party has the receipt, the *witness*
   (pre-state + private inputs + the byte-for-byte effect sequence the
   executor ran), and the proof. They call `generate_effect_vm_trace` on
   the witness, confirm the trace's derived PI vector matches the
   receipt's recorded PI, and then verify the proof against that PI. This
   is the *honest mirror*: a redundant check that the prover ran the
   right computation. It catches a class of attacks the proof system
   alone cannot: a buggy prover that produced a proof for trace T but
   claimed PI from trace T' (which the soundness of the AIR should
   already preclude, but bugs happen at the gluing layer between
   `generate_effect_vm_trace` and `stark::prove`).
3. **Re-execute the turn.** Third party has the receipt, the original
   `Turn`, the cell's pre-state, and `TurnExecutor` source. They re-run
   `TurnExecutor::execute` against a ledger snapshot reconstructed from
   the previous receipt's `post_state_hash` plus the witnessed cell
   state, and check the new `post_state_hash` and `effects_hash` match.
   This catches everything (1) and (2) do, *plus* divergence between
   the AIR's modeled semantics and the executor's actual semantics. But
   it requires the executor to be deterministic — and today it is not
   quite: timestamps are read from the federation clock at commit time,
   pipelined sends interact with the wider gossip log, fast-path
   threshold signatures involve other nodes' signatures.
4. **Full Byzantine replay.** Third party reconstructs the entire
   federation history from gossip + witnesses. Useful for forensic audit
   of the federation itself; massively over-scope for "constrain my
   behavior in the future."

**Recommendation: scope (2), Re-derive trace + verify.** The user's
framing ("within a margin useful for constraining future behavior")
matches this exactly. (1) is too weak — it doesn't constrain the prover,
only the proof. (3) is too strong — it makes the substrate's
determinism a load-bearing assumption and forces the executor onto a
gnarly determinization path that other work streams already touch
(timestamp-trapdoor effects, sovereign-cell proof-carrying turns) but
that we should not block this work on. (2) is the smallest jump that
gives a verifier the ability to say *both* "the proof is valid" and
"the prover ran the right computation on the right inputs," which is
what "replay" colloquially means.

Where (3) is genuinely needed (regulatory audit, dispute resolution),
the `WitnessedReceipt` produced by scope (2) is a strict prefix of what
scope (3) would need — adding the original `Turn` and a determinism
clamp later is additive, not breaking. So (2) is also the right
*progression point*.

## 2. `WitnessedReceipt` struct sketch

```rust
/// A `TurnReceipt` enriched with sufficient material for trace re-derivation.
/// This is the on-disk / wire shape; in-memory we still pass `TurnReceipt`
/// around hot paths and lift to `WitnessedReceipt` only for archival,
/// audit-export, or `pyana-verifier` consumption.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WitnessedReceipt {
    /// The receipt itself. Unchanged from today, so existing chains stay valid.
    pub receipt: TurnReceipt,

    /// Identity of the AIR that proved this turn. For v1 always
    /// `pyana-effect-vm-v1`; future versions may carry per-cell program VKs.
    pub air_name: String,

    /// STARK proof bytes (`stark::proof_to_bytes` output). Verifiable
    /// stand-alone via `verifier::verify_effect_vm_proof`.
    pub proof_bytes: Vec<u8>,

    /// Public inputs as a flat u32 vector (BabyBear canonical form).
    /// Redundant with `proof.public_inputs` but extracted for replayer
    /// convenience — avoids deserialising the proof just to read PI.
    pub public_inputs: Vec<u32>,

    /// The witness bundle. Optional at the API boundary: a receipt
    /// without a witness is still a (scope-1) verifiable artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub witness: Option<WitnessBundle>,

    /// Hash of the witness bundle (committed even when the bundle itself
    /// is absent or encrypted). Allows the chain to bind to a specific
    /// witness without revealing it. Computed as Blake3 over the
    /// post-card-serialized `WitnessBundle`.
    pub witness_hash: [u8; 32],

    /// Cross-cell aggregation hook (see STAGE-7-GAMMA doc).
    /// When this receipt is later aggregated, the aggregator carries
    /// this WR's `witness_hash` along — the aggregate proof binds to
    /// all per-cell witness hashes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub aggregate_membership: Option<AggregateMembership>,
}

/// The witness material itself. Sufficient (combined with the AIR
/// definition) to call `generate_effect_vm_trace_ext` and reproduce
/// `public_inputs` byte-for-byte.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WitnessBundle {
    /// The cell state as it entered the turn. Includes all 8 field
    /// elements, balance, nonce, c-list, etc. — everything the trace
    /// generator consumes.
    pub pre_state: pyana_cell::state::CellState,

    /// The effect sequence the executor produced. NOT the original `Turn`
    /// — that may not survive (it's been validated, decomposed, and
    /// stripped of e.g. preconditions that no longer matter). This is
    /// the post-validation flat effect list that the AIR consumed.
    pub effects: Vec<pyana_circuit::effect_vm::Effect>,

    /// EffectVm extra context (block height, max custom effects,
    /// handoffs root). Required to reproduce the widened PI layout.
    pub context: SerializableEffectVmContext,

    /// Truly-secret inputs: opening data for value commitments, note
    /// preimages, escrow blindings, conservation-proof scalars, etc.
    /// These never appear in `pre_state` or `effects` (which only carry
    /// commitments) but ARE part of what the executor needed to validate
    /// the turn. Tagged so the replayer knows where each item plugs in.
    pub secrets: Vec<SecretInput>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum SecretInput {
    /// Pedersen blinding for a note's value commitment.
    NoteBlinding { commitment: [u8; 32], blinding: [u8; 32], value: u64 },
    /// Sealed-box content (the ciphertext is public; the key is here).
    SealedBoxKey { box_id: [u8; 32], key: [u8; 32] },
    /// Schnorr conservation proof scalar (excess-binding witness).
    ConservationExcess { scalar: [u8; 32] },
    /// Custom-program private input bundle, opaque to the substrate.
    CustomProgram { program_vk: [u8; 32], blob: Vec<u8> },
}
```

Approximate sizes:

* Receipt today: ~600 bytes serialized (postcard).
* Witness bundle for a small turn (1 effect, no notes): ~400 bytes.
* Proof bytes: dominated by FRI commitments + query proofs, ~25–80 KB
  for the Effect VM AIR at production-grade trace_len.
* Witness for a many-note turn (8 NoteSpend/NoteCreate pairs with
  blindings): ~2 KB.

Total per-turn footprint: ~30–100 KB. For a chain of 10 000 turns that's
~1 GB — fine for archival, painful for hot storage.

## 3. Witness storage strategy

Three candidates:

* **A. Prover-local witness.** The prover writes `.witness.bin` alongside
  the receipt in their own storage. `witness_hash` ships in the chain;
  the bundle never leaves the prover's machine. Nobody else can replay
  scope (2), but the prover *can*, at any time, demonstrate replayability
  to a chosen third party by handing over the bundle. Privacy default:
  closed.
* **B. Witness encrypted to a recovery authority.** The prover encrypts
  the bundle under (e.g.) `crypto_box`/`age` to a named recovery party's
  public key — a sovereign federation operator, a swing-pull replay
  authority, an enterprise compliance keypair, or a Shamir threshold
  set of any of the above. The ciphertext ships in the chain (or is
  pinned to content-addressable storage and referenced by hash); only
  the authority can decrypt. Privacy default: open-to-authority.
* **C. Public/private bifurcation by trust boundary.** Anything that
  already appears in the proof's public inputs (state commitments,
  nullifiers, value commitments) is part of the receipt-side
  `WitnessBundle` and travels with the chain in cleartext.
  Truly-secret material (note preimages, blindings, sealed-box keys,
  custom-program private blobs) ships in a separate optional bundle
  with its own access-control scheme — typically (B). Privacy default:
  hybrid.

**Recommendation: (A) as the v1 default, with (C) as the structural
shape and (B) as an opt-in extension.**

Reasoning:

* The user said "within a margin useful for constraining future
  behavior." That margin is precisely "the prover can choose to enable
  replay later." (A) is the strategy that delivers this with zero
  trust assumptions on third parties.
* (C) is the *shape* we want even under (A): the on-chain
  `WitnessBundle` field should be split into a "public-witness" half
  (`pre_state`, `effects`, `context`) and a "private-witness" half
  (`secrets`). Then the prover has a real choice: ship the public half
  with the chain (small, low-sensitivity), keep the private half local.
  This costs almost nothing structurally and immediately enables a
  partial-replay mode where third parties verify everything except
  the secrets.
* (B) becomes a thin policy layer over (C): the prover encrypts the
  private half to a recovery authority instead of (or in addition to)
  keeping it local. We do not need to design (B) in detail now; the
  `secrets` field's serialized bytes are exactly what (B) encrypts.

Concretely:

```rust
pub enum WitnessAvailability {
    /// Full witness in-line (this WR is self-contained for replay).
    Inline(WitnessBundle),
    /// Public half in-line; private half stored at an addressable
    /// location (CID, filesystem path, recovery-authority pointer).
    Split { public: PublicWitness, private_ref: PrivateWitnessRef },
    /// Public half in-line; private half encrypted to a named authority.
    Encrypted { public: PublicWitness, ciphertext: Vec<u8>, authority: RecoveryAuthority },
    /// Nothing in-line; witness_hash is the only commitment.
    Sealed,
}
```

`WitnessBundle::witness` in the struct sketch above becomes this enum.

## 4. Chain-level structure

A `WitnessedReceipt` per turn aggregates into what?

**Option α — flat Vec.** `Vec<WitnessedReceipt>`, replayed in order.
Linear in chain length to verify. Simplest. Storage cost grows
linearly. Fine for chains up to ~10⁴ turns.

**Option β — IVC-folded chain.** Each `WitnessedReceipt` carries a
folded IVC proof that the chain up-to-and-including this turn is
internally consistent. Equivalent to today's `pyana_compress_history`
but witness-aware: the IVC step's witness is *itself* the prior step's
PI plus the current `WitnessBundle::witness_hash`. Verifier work is
constant in chain length (one IVC verify), but you cannot replay
*individual turns* without keeping their witnesses around — the IVC
only proves the chain held *some* witness with that hash.

**Option γ — Merklized accumulator.** Receipts form leaves of a Merkle
tree (or sparse Merkle tree keyed by turn-number); a single root
commits to the whole history. Witnesses are stored separately
(content-addressed by `witness_hash`). To replay turn N: present
inclusion proof of `receipt_N` under the root, then run scope-(2)
replay against the witness blob.

**Recommendation: hybrid.** Maintain Option α as the canonical wire
shape (it's what the wallet's `receipt_chain` already produces) and
add Option γ as an optional accumulator commitment that the executor
publishes alongside each receipt (the Merkle root over receipts so far).
Option β remains the "compression" mode invoked by
`pyana_compress_history` for telling outsiders "this chain is N turns
long and internally consistent" without shipping all N receipts.

**Interaction with capability revocation.** A revoked-cap exercise
should appear in the chain as a `Rejected` action, not as a gap. The
current executor emits no receipt for rejected turns — the rejection is
visible only in mempool / wallet logs. For replayability we want
rejection-receipts: a `TurnReceipt`-like artifact that records "turn
T attempted, failed at action i with reason R, no state change." This
deserves its own enum variant on the chain:

```rust
pub enum ChainEntry {
    Committed(WitnessedReceipt),
    Rejected(RejectedReceipt),  // turn_hash + reason + at_action + previous_receipt_hash
}
```

A future replayer can then prove "this cap was revoked and a later
attempt to exercise it was rejected" — that's a structurally
important property and a hole in today's chain.

**Interaction with federation forking.** Two valid histories of the
same cell can exist if the federation forks. `receipt.federation_id`
already binds each receipt to one fork; a `WitnessedReceipt` inherits
this. A third party can ingest two chains, verify both, and report the
fork point. We add no new primitives here; we just don't accidentally
strip `federation_id` from the witness side.

## 5. Replayer API

A natural extension of `pyana-verifier`:

```rust
// in verifier/src/lib.rs (additive)
pub struct ReplayInput {
    pub witnessed_receipts: Vec<WitnessedReceipt>,
    /// Optional: cell state at the start of the chain. If absent, the
    /// replayer assumes a fresh genesis state.
    pub initial_state: Option<pyana_cell::state::CellState>,
}

pub struct ReplayOutput {
    pub verified_count: usize,
    /// First index where replay diverged from the receipt's claims.
    pub diverged_at: Option<usize>,
    pub reason: String,
}

pub fn replay_chain(input: ReplayInput) -> ReplayOutput { ... }
```

For each `WitnessedReceipt`:

1. **Public-input check.** Recompute PI from `witness.pre_state` and
   `witness.effects` via `generate_effect_vm_trace_ext`. Confirm equals
   `wr.public_inputs`.
2. **Proof verification.** Call `verify_effect_vm_proof(&wr.proof_bytes,
   &wr.public_inputs, vk_hash)`.
3. **Receipt linkage.** Confirm `wr.receipt.previous_receipt_hash`
   matches the previous WR's `receipt.receipt_hash()`.
4. **State linkage.** Confirm `wr.receipt.pre_state_hash` equals
   `witness.pre_state.compute_commitment()` and post-state is the
   trace's terminal state commitment.
5. **Effect-hash linkage.** Recompute `compute_effects_hash(&effects)`,
   confirm equals `wr.receipt.effects_hash`.

Performance: linear in chain length; per-turn cost dominated by STARK
verify (~10–50 ms). For chains over ~10³ turns, optionally call into
the IVC-compressed proof for a constant-time end-to-end check
(this is the existing `verify_ivc_stark` path), accepting that the IVC
verdict says "chain is consistent" but not "each turn's witness was
honest" — that part still requires per-turn scope-(2) work.

The replayer is a *pure* function: input bytes, output verdict. No
network, no shared state. Same OS-process isolation as today's
`pyana-verifier`. The user can pipe a chain to a separate process,
get a yes/no, and walk away — which is what makes this trust-minimal.

## 6. Integration with `pyana_compress_history`

Today's `tool_compress_history` (`node/src/mcp.rs:2250`) calls
`prove_ivc_stark(initial_root, &new_roots)`, producing a single proof
that the chain of state roots is well-formed. The witness — the
per-turn effect sequences and pre-states — is discarded; the IVC step
function just folds root-i into root-(i+1).

To make this witness-aware:

* The IVC step function should take, as private input, the
  `WitnessBundle::witness_hash` for each step.
* The IVC public input grows by one field element: a running
  Poseidon2-accumulator over all witness hashes (a "transcript root"
  of witnesses).
* On compression, the prover provides
  `Vec<witness_hash>` and the IVC proves: "for each step i, applying
  effects with hash H_i to pre-state with hash P_i yields post-state
  with hash P_{i+1}, AND the accumulator A_i = Hash(A_{i-1}, H_i)."
* The final compressed proof binds the chain to a 32-byte accumulator
  value. A future replayer, given the witnesses, can recompute the
  accumulator and confirm it matches.

Critically, **the IVC's own witness still gets discarded.** What we
gain is that the IVC's *public* output now constrains the per-step
witness hashes, so a holder of those witnesses can later prove they
correspond to the chain the IVC compressed.

This is the smallest semantic change that bridges "compressed" and
"replayable." The expensive part — generating per-turn witnesses — is
unchanged.

## 7. Adversarial replay

**Malicious replayer.** A replayer can refuse to acknowledge a valid
chain, or produce a misleading natural-language verdict. They cannot
forge an "accepted" verdict because the verdict embeds the input chain
hash and the verifier is a pure function — running it locally always
beats trusting a replayer's report.

A replayer with the *private* witness half (strategy B/C) can also
learn the prover's secrets. This is the cost of opting into a recovery
authority. Strategy A avoids this cost at the price of replayability.

**Malicious prover.** With strategy (A) and `Sealed` availability,
the prover can:

* **Lie about which witness produced the trace.** The STARK soundness
  precludes proof-forgery, but the prover can later claim
  "the witness was X" and present an X that re-derives PI identically
  to the actual witness Y. This is only possible if two distinct
  witnesses produce identical PI — which for the Effect VM AIR
  requires identical pre-state, effects, and context (since these are
  the PI's preimage). So the prover is constrained: they can lie about
  `secrets`, which don't enter PI, but they cannot lie about
  `pre_state` or `effects` without contradicting the proof.
* **Refuse to reveal the witness.** Strategy (A)'s feature is also its
  bug: a prover who later refuses cooperation is indistinguishable
  from one who never had a valid witness. Mitigation: a *commit-to-
  witness* step at proving time, where `witness_hash` is included in
  the receipt-chain hash (already done in the struct sketch). Now the
  prover is bound to a specific witness; they can refuse to reveal,
  but they cannot substitute. A counter-party who later acquires the
  witness independently (e.g., subpoena, forensic recovery) can
  validate it against the committed hash.
* **Encrypt to an authority they control.** Strategy (B) requires the
  named authority to be a third party. Document this requirement;
  consider a substrate-level check that the recovery-authority pubkey
  is in a registered set.

## 8. Recommended path

Smallest first step that lands a real `WitnessedReceipt`:

1. Add the `WitnessedReceipt` struct in `turn/src/turn.rs` (or a new
   `turn/src/witnessed.rs`). Required fields: `receipt`, `air_name`,
   `proof_bytes`, `public_inputs`, `witness: Option<WitnessBundle>`,
   `witness_hash`. Aggregate-membership field deferred to the gamma
   work.
2. Plumb construction at exactly one site: the executor's
   commit path that today builds the Effect VM proof. When the proof
   is generated, the trace and PI are already in hand — capture them
   into a `WitnessBundle` and pair it with the proof bytes. Cost:
   ~50 lines in `executor.rs`. Default to in-line witness (strategy A,
   `Inline` availability) — no encryption yet.
3. Extend `pyana-verifier` with a `replay-chain` subcommand reading a
   JSON / postcard array of `WitnessedReceipt`. Implementation: the
   loop in §5 above.
4. Add a single demo path: the existing demo binary (or the MCP tool)
   exports a chain of `WitnessedReceipt` to disk, and we ship a
   tiny replayer invocation showing scope-(2) replay end-to-end.

What this delivers:

* A real on-disk artifact a third party can run against an unmodified
  `pyana-verifier` binary and get scope-(2) replay.
* A migration path: existing `TurnReceipt` chains keep working because
  `WitnessedReceipt` is a strict super-set with the receipt nested.
* A binding point for the gamma work: when cross-cell aggregation
  lands, it just adds the `aggregate_membership` field; the witness
  side is already wired.

What it leaves open:

* **Encryption / recovery authority (strategy B).** Optional, not
  needed for v1.
* **Public/private witness bifurcation.** Strategy C is the next
  refinement after v1 ships; v1 keeps witnesses opaque.
* **IVC witness-awareness (§6).** Requires modifying
  `prove_ivc_stark`; deferred until the simple Vec replayer is
  exercised.
* **Determinism for scope (3).** Requires timestamp-trapdoor effects
  plus removing nondeterministic executor reads. Not a v1 goal.
* **Rejection receipts.** A separate hole in today's chain (§4);
  worth tracking but not blocking the witness work.

The bet: by putting a real `WitnessedReceipt` in front of one
end-to-end demo (export, ship to a separate verifier process, replay,
get a verdict), we make the abstract notion of "replayable chain"
concrete and testable. Every later refinement — encryption,
aggregation, IVC-binding, determinism — is additive on this skeleton.

---

### Cross-references

* `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` (parallel work): cross-cell
  binding of receipts. Where this doc adds the *vertical* witness
  dimension (each receipt gains a witness), gamma adds the *horizontal*
  aggregation dimension (multiple cells' receipts combined). The
  `aggregate_membership` field in `WitnessedReceipt` is the bridge.
* `STAGE-7-PLUS-DESIGN.md`: parent design context for stage-7 work.
* `DESIGN-receipts.md`: the original receipt-chain design (pre-witness).
* `verifier/src/lib.rs`: target home for the replayer.
* `spec/CellModel.tla`: invariants the substrate guarantees
  (`ReceiptChainIntegrity`, `BalanceConservation`, etc.). A
  witnessed-receipt replayer can in principle check these too,
  becoming a runtime witness to the TLA invariants.
