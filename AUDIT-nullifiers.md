# AUDIT — Nullifiers in pyana

**Question:** what is a nullifier in pyana, who computes it, who checks it, and
where is the binding incomplete?

**Short answer:** nullifiers exist and are heavily relied on, but the word names
**at least five distinct, mutually-incompatible mechanisms** that share only the
shape "publish a one-way value to mark a thing consumed". The flagship note
nullifier (Zcash-shape) is cryptographically well-derived and well-bound inside
the STARK, but its **post-spend ledger binding is incomplete**: in the
production executor path (`turn/src/executor.rs`) note spends are *journaled*
but never inserted into a `NullifierSet`. The double-spend gate exists
in code (`cell/src/nullifier_set.rs`, `store/src/note_tree.rs`) but no
production caller invokes it. Bearer caps are **not** nullifier-shaped — they
are expiry+revocation-channel-shaped, which is a different (and weaker) design
choice. A bridge security property (cross-federation replay binding) is
**claimed** to be enforced inside the STARK but is in fact **not** (the AIR has
no boundary constraint for `destination_federation`).

---

## 1. Inventory of `nullifier` in the source

`grep -ri nullifier` returns ~700 hits across the tree. They group into five
distinct semantic clusters:

### 1a. Note nullifiers (Zcash-shape) — the flagship
- `cell/src/note.rs:31` — `pub struct Nullifier(pub [u8; 32])`.
- `cell/src/note.rs:179` — `Note::nullifier(spending_key)`:
  `BLAKE3_derive_key("pyana-note nullifier v1", commitment || spending_key || creation_nonce)`.
- `cell/src/nullifier_set.rs` — `NullifierSet` (BTreeSet + Merkle tree with
  domain-separated leaf/node hashes and adjacent-neighbor non-membership
  proofs).
- `circuit/src/note_spending_air.rs:166` — in-circuit recomputation:
  `Poseidon2(commitment, key[0..8], creation_nonce)`.
- `circuit/src/dsl/note_spending.rs:101-129` — DSL version, two-step Poseidon2
  hash because of the 5-arity hash bound.
- `store/src/note_tree.rs:164` — `PersistentNullifierSet` (redb-backed).

This is the design any reader who has seen Zcash/Penumbra/Aztec recognises.

### 1b. Bridged-note nullifiers (cross-federation double-bridge tracking)
- `cell/src/note_bridge.rs:238-293` — `BridgedNullifierSet`: a sorted `Vec`
  that the destination federation uses to reject re-presentation of the same
  source-fed proof.
- `turn/src/executor.rs:524` — `pub bridged_nullifiers: Mutex<BridgedNullifierSet>`.
- `turn/src/executor.rs:5020-5036` — `BridgeMint` inserts into it and
  journals for rollback (`record_bridged_nullifier_inserted`).
- `cell/src/note_bridge.rs:391-447` — `PendingBridgeSet` keyed by nullifier:
  Phase-1 lock indexes a *pending* bridge under the spent note's nullifier.

This is the only nullifier set wired all the way through to the executor and
rolled back via the journal.

### 1c. Proof nullifiers (conditional / discharge replay prevention)
- `turn/src/conditional.rs:191-225` — `resolve_condition` keeps a
  `HashSet<[u8;32]>` of `proof_hash`; second presentation of the same proof
  fails with `"proof already used"`.
- `turn/src/conditional.rs:227-262` — `compute_proof_hash` uses
  `BLAKE3_derive_key("pyana-proof-nullifier-v1", ...)`.
- `node/src/state.rs:94` / `node/src/api.rs:2089-2110` — the node persists
  "proof nullifiers" (used proof hashes) in the store on receipt, with a
  warning log if persistence fails.

This is named "nullifier" but is just *proof replay protection over a
content-addressed hash*. There is no holder secret. Anyone who sees the proof
sees the nullifier.

### 1d. Stake nullifiers (anti-Sybil for gossip)
- `intent/src/lib.rs:520-559` — `compute_stake_nullifier(commitment, epoch, counter)`:
  Poseidon2 over (commitment, epoch, counter) post-hashed with
  `BLAKE3("pyana-stake-nullifier-v1", ...)` to lift back to 32 bytes.
- `intent/src/gossip.rs:236-303` — `used_stake_nullifiers: HashSet<[u8;32]>`,
  cleared every epoch boundary.

Epoch-scoped (the set is *erased*, not appended). Privacy-preserving
rate-limit, not a permanent "spent" record.

### 1e. Solo / federation nullifier log (sequencer-mode replay protection)
- `federation/src/solo.rs:91-260` — `NullifierLog`: a signed, ordered log of
  nullifier insertions during solo-mode operation; entries carry node
  signatures so rejoiners can verify the sequence.
- `node/src/api.rs:1183-1193` — solo mode records nullifiers from each turn
  into the `NullifierLog`.

### 1f. Other uses
- `chain/src/credential.rs:226-239` — `compute_presentation_nullifier(serial, action_domain)`
  for anonymous-credential sybil resistance.
- `chain/src/withdraw.rs:178-...` — withdrawal-style nullifier
  (`blake3("pyana-nullifier-v1", nullifier_key || note_commitment)`) — note
  this is a **different domain string** and a **different derivation** from
  the note nullifier in `cell/src/note.rs`. Either this is dead/parallel
  code, or there are two incompatible note flavours.
- `types/src/lib.rs:207` — `Checkpoint::nullifier_set_root: Option<[u8;32]>`:
  protocol-level field for committing to the nullifier-set root, with
  unambiguous-encoding tests at 306-322. Used in `node/src/api.rs:2929`.
- `token/src/revocation.rs` — token revocation. This is **not** called
  "nullifier" in code but shares the shape (sorted Merkle tree, non-membership
  proofs); the file explicitly cross-references `nullifier_set.rs` as its
  pattern (line 305).
- `tokens/` does not exist as a path; the token revocation lives in `token/`.

---

## 2. Note nullifier derivation: well-bound

The flagship Zcash-shape nullifier IS cryptographically sound at the derivation layer:

| Property                              | Where enforced                                                                 |
|---------------------------------------|--------------------------------------------------------------------------------|
| Holder secret required                | `Note::nullifier(spending_key)` mixes `spending_key` into hash (`note.rs:179`) |
| 248-bit key (not 31)                  | `SPENDING_KEY_LIMBS = 8`, all 8 limbs hashed (`note_spending_air.rs:64,166`)   |
| Position-independent (fed-portable)   | Derived from `commitment || key || creation_nonce`, no tree position (`note.rs:26-30, 173-186`) |
| Unique per note                       | `creation_nonce` is per-note random; doc + test at `note.rs:348-359`           |
| Bound to public inputs in STARK       | Boundary at row 0 col `NULLIFIER` (`note_spending_air.rs:480-484`)             |
| Value/asset bound to STARK            | Boundary at row 0 col `VALUE` / `ASSET_TYPE` (`note_spending_air.rs:494-509`)  |
| In-circuit Poseidon2 recomputation    | Constraint C4 in the DSL (`dsl/note_spending.rs:117-129`)                      |
| Single-limb tamper detected           | `flipping_single_key_limb_changes_nullifier` (`note_spending_air.rs:1194`)     |

The derivation in `cell` (BLAKE3) and the derivation in `circuit` (Poseidon2)
use **different hashes** — the BLAKE3 form is documented as the cleartext-side
nullifier and the Poseidon2 form is what the STARK enforces. The `Note` struct
exposes `commitment()` (BLAKE3) and `poseidon2_commitment()` (`note.rs:204-255`)
explicitly to flag this dual identity, but `Note::nullifier()` only emits the
BLAKE3 form. The Poseidon2 nullifier lives only inside
`NoteSpendingWitness::nullifier()` (a `BabyBear` field element). **This is a
latent bug surface**: when a `NoteSpend` effect carries a `Nullifier([u8;32])`
*and* a STARK proof whose public input is a `BabyBear`, the executor must
either reconcile or pick one. See §7 for what it actually does.

---

## 3. Note nullifier check: incomplete (production executor)

`turn/src/executor.rs:4873-4943` (`Effect::NoteSpend`):

```rust
// Validate nullifier is well-formed (non-zero). ...
// Verify the ZK spending proof... public_inputs = nullifier || root || value || asset_type
if !verifier.verify(spending_proof, "note-spend", "note-tree", &public_inputs) { ... }
// Record for the note layer to process after turn commits.
journal.record_note_spend(*nullifier);
Ok(())
```

The journal entry `JournalEntry::NoteSpend { nullifier }` is created — and
then **discarded**. Both the rollback path (`turn/src/journal.rs:440-451`) and
the delta-computation path (`turn/src/executor.rs:8039-8055`) explicitly say
"these are simply discarded — the note layer ... only process them after a
successful commit". Searching the entire repo:

```
$ grep -rn 'JournalEntry::NoteSpend|JournalEntry::NoteCreate' --include='*.rs'
turn/src/journal.rs:220   (write)
turn/src/journal.rs:440   (discard on rollback)
turn/src/executor.rs:8040 (discard during delta computation)
```

There is no third consumer. The promised "note layer" that processes the
entries post-commit **does not exist in code**.

Independently, `store/src/lib.rs:578-614` defines `spend_note_atomic(nullifier,
new_commitment) -> Result<u64>` which is the obvious place to wire this through
— and it has the correct double-spend semantics (`"nullifier already spent
(double-spend)"` at line 590). But:

```
$ grep -rn 'store_nullifier|spend_note_atomic|is_nullifier_spent' --include='*.rs' | grep -v /store/
(no matches)
```

**No production code calls it.** The only place a `NullifierSet` is actually
populated by note spends is `wasm/src/runtime.rs:267-283`
(`PyanaRuntime::spend_note`) — i.e. the browser simulator. The proptest in
`cell/tests/proptest_nullifier.rs` exercises `NullifierSet` directly, not
through the executor.

**Consequence:** a `NoteSpend` effect that passes STARK verification once can
be presented again in a later turn and will pass again. The STARK proof says
"someone who knew the secret derived this nullifier from a note in a tree with
this root"; nothing on the executor side says "and this nullifier has not been
spent before". The proof itself is replayable.

---

## 4. Bridge nullifier check: works for *bridges*, doesn't help local

The bridged-nullifier path *is* wired all the way through:

- `executor.rs:5020-5031` — `BridgeMint` inserts `portable_proof.nullifier`
  into `self.bridged_nullifiers`; `.insert()` returns `Err(AlreadyBridged)`
  on duplicate (`note_bridge.rs:262-271`).
- `executor.rs:5036` — recorded in the journal as
  `BridgedNullifierInserted` so a failed turn doesn't permanently burn the
  nullifier (rollback at `journal.rs:429-431`).
- `note_bridge.rs:415-431` — `PendingBridgeSet::insert` rejects an
  already-locked nullifier (Phase-1 lock idempotency).

This protects the destination federation against double-mint, but the *source*
federation still doesn't add the burned nullifier to any permanent set. The
Phase-3 `finalize_bridge` (`executor.rs:5074-...`) does **not** insert into
`bridged_nullifiers` either, because that set is meant for *inbound* not
*outbound*. The source's permanent-burn record is the empty
`NullifierSet`-shaped hole described in §3.

---

## 5. Bridge `destination_federation` binding: claimed but not enforced

`cell/src/note_bridge.rs:78-97` — the docstring is explicit:

> The `destination_federation` field cryptographically binds this proof to a
> single target federation. It is included in the STARK proof's public inputs,
> so the same spending proof cannot be replayed against a different federation.

`note_bridge.rs:1230-1233`:

> NOTE: The note_spending AIR must embed value and asset_type as public inputs
> for this check to be meaningful. If the current AIR does not include them,
> the verify_stark closure should reject the proof (fail-closed).
> TODO: Ensure NoteSpendingAir includes value and asset_type in public inputs.

Looking at `circuit/src/note_spending_air.rs:99-109`:

```rust
pub mod pi {
    pub const NULLIFIER: usize = 0;
    pub const MERKLE_ROOT: usize = 1;
    pub const VALUE: usize = 2;
    pub const ASSET_TYPE: usize = 3;
}
```

There is **no `DESTINATION_FEDERATION` public input**. The boundary
constraints in `note_spending_air.rs:471-512` bind only those four indices.
The DSL version (`circuit/src/dsl/note_spending.rs`) has the same four
boundary slots (`BoundaryRow`s at the top of the file enumerate them).

Meanwhile `turn/src/executor.rs:4976-4982` (the bridge-mint verify closure):

```rust
public_inputs.extend_from_slice(nullifier);          // 32
public_inputs.extend_from_slice(root);                // 32
public_inputs.extend_from_slice(dest_federation);     // 32  <-- NEW
public_inputs.extend_from_slice(&value.to_le_bytes()); // 8
public_inputs.extend_from_slice(&asset_type.to_le_bytes()); // 8
```

The `dest_federation` bytes go into the verifier's public-input vector, but
the AIR has no boundary or constraint that consumes those bytes. The
verifier's `verify(proof, action, resource, vk)` signature
(`turn/src/executor.rs:99`) treats the last arg as a verification key + public
inputs blob; how the STARK backend slices that into typed BabyBear elements
determines whether the extra 32 bytes are silently ignored, or cause a
length-mismatch failure (closing the hole accidentally), or are reinterpreted
into the existing 4 PI slots (catastrophic — same nullifier replays across
federations because PI slot 0 is now the destination prefix).

**This is at minimum a documentation/code gap; in the worst case it is the
inflation bug the docstring warns against.** A bridge mint test that *actually
varies* `destination_federation` and confirms rejection should be added. (The
turn-level tests I saw in `tests/src/adversarial_pipeline.rs` exercise the
nullifier-replay path against the *bridged* set, not the destination binding.)

---

## 6. Bearer caps: not nullifier-shaped

`turn/src/action.rs:120-148` — `BearerCapProof`:

- carries `expires_at: u64` (mandatory, attenuates the revocation window),
- optional `facet_mask: u32` (E-language facet attenuation),
- optional `revocation_channel: ChannelId` pointing into a
  `RevocationChannelSet` (`cell/src/revocation_channel.rs`),
- a delegation chain proof (`DelegationProof`).

There is **no one-time-use token, no nullifier, and no presentation counter**.
A bearer cap with `expires_at = h_max` can be exercised repeatedly between
issuance and expiry, as many times as the bearer likes, against as many turns
as they like, until either the height exceeds `expires_at` or the channel
trips. This is biscuit/macaroon-ancestry behaviour, not Zcash-ancestry.

`token/src/revocation.rs:546-636` provides a `RevocationRegistry` whose
`is_revoked()` is the runtime equivalent of "is this nullifier in the spent
set", but only the **issuer** revokes (not the holder by use), and
non-membership proofs are presented offline. The `RevocationChannel` runtime
gate (executor-side) is checked at exercise time, but again the channel is
*tripped by the revoker*, not by the holder consuming the cap.

If we wanted bearer caps to be one-shot, we would need a "presentation
nullifier" tracked per (cap_id, presentation_counter) or per
(serial, action_domain). `chain/src/credential.rs:226-239`'s
`compute_presentation_nullifier(serial, action_domain)` is the right shape —
but it lives in the anonymous-credential code path, not in the bearer-cap
exercise path. **The two shapes are not unified.**

---

## 7. Open trapdoor: `Nullifier([u8;32])` vs `BabyBear` PI

The executor's note-spend public-inputs construction
(`executor.rs:4928-4932`):

```rust
let mut public_inputs = Vec::with_capacity(80);
public_inputs.extend_from_slice(&nullifier.0);     // 32 raw bytes
public_inputs.extend_from_slice(note_tree_root);   // 32 raw bytes
public_inputs.extend_from_slice(&value.to_le_bytes());     // 8
public_inputs.extend_from_slice(&asset_type.to_le_bytes()); // 8
```

But the AIR's boundary constraint compares `BabyBear` field elements
(`note_spending_air.rs:480-509`). A `Nullifier` is 32 bytes; a `BabyBear` is
~31 bits. The witness's `.nullifier()` produces a single `BabyBear`
(`note_spending_air.rs:166-173`). Somewhere between the executor and the AIR,
the 32-byte nullifier must be either truncated, hashed, or expanded to
match. Three possibilities:

1. The verifier reduces the 32 bytes to a single BabyBear by `u32::from_le_bytes(first 4)
   mod p`. Then **collisions are trivial** — many different `Nullifier`s
   hash-collide on the AIR PI, and a spender can claim any of them.
2. The verifier splits the 32 bytes into 8 limbs and the AIR is silently
   expected to have 8 PI slots for the nullifier. Then the 4-slot PI vector
   does not match.
3. The verifier rejects on length mismatch, in which case `NoteSpend`
   *never verifies in production*.

I did not run the proof to distinguish (1)/(2)/(3) — the harness's
`verifier.verify(...)` is a trait method whose concrete impl lives in
`wire/src/server.rs`, and the implementation does not slice the buffer into
typed PIs in any of the cases I read. **Recommend tracing one real `NoteSpend`
end-to-end before trusting any other claim in this audit.**

(The DSL note-spending path is the canonical one going forward — see the
`#[deprecated]` attributes at `note_spending_air.rs:252,519,530`. So the
relevant code to read is `circuit/src/dsl/note_spending.rs:73-...` and
whatever `pyana_circuit::stark::verify` does with the public-input bytes.
Out of scope for this audit; the bug surface is the same regardless of which
proving path.)

---

## 8. Privacy: where nullifiers help and where they don't

Zcash-shape nullifiers do help here: §1a's derivation reveals nothing about
the spending key (collision-resistant hash) and the AIR keeps the key in the
witness, never the PI. The `creation_nonce` ensures even an attacker who
guesses the owner and value still cannot recompute the nullifier from
on-chain state alone. **The privacy properties of the derivation are sound.**

What is *not* sound is the **post-spend ledger commitment**: because the
permanent `NullifierSet` is not populated (§3), the
`Checkpoint::nullifier_set_root` field (`types/src/lib.rs:207`) — which is
how a verifier off-chain would check non-spent-ness — is either always None
or always reflects an empty set in non-WASM deployments. Privacy-preserving
spend semantics need *both* (a) a hiding nullifier derivation (we have this)
and (b) a public nullifier set committed to by consensus (we don't, in
the production executor path).

The `NoteBatcher` (`cell/src/note.rs:471-558`) addresses a separate privacy
concern (timing-correlation on commitments, not nullifiers). The bridge
nullifier set is *not* private — nullifiers are committed in cleartext in
`PortableNoteProof.nullifier` (`note_bridge.rs:88`).

---

## 9. Nullifier inventory

| # | Location | What is "nullified" | Who derives | Who checks | Lifecycle |
|---|---|---|---|---|---|
| 1a | `cell/src/note.rs:179` | A note (one-time-spend) | Holder w/ `spending_key` | `NullifierSet::insert` (`cell/src/nullifier_set.rs`) | Append-only, set root in checkpoint |
| 1a' | `circuit/src/dsl/note_spending.rs` | Same note (in-circuit form) | STARK prover | Boundary constraint in DSL Air | Bound to PI slot 0 |
| 1b | `cell/src/note_bridge.rs:88` | A cross-fed bridge claim | Destination fed | `BridgedNullifierSet::insert` (`executor.rs:5020`) | Append-only per-fed, rolled back on turn fail |
| 1b' | `cell/src/note_bridge.rs:326` | A *locked* outbound note | Source fed | `PendingBridgeSet::is_locked` | Pending → Finalized/Cancelled |
| 1c | `turn/src/conditional.rs:227` | A presented proof | Anyone | `used_proof_hashes: HashSet` | Per-resolver-call, optionally persisted |
| 1c' | `node/src/state.rs:94`, `api.rs:2089` | Same proof, node-wide | Node | `proof_hashes` table in store | Persistent |
| 1d | `intent/src/lib.rs:528` | (commitment, epoch, counter) for staking | Note holder | `IntentGossip::used_stake_nullifiers` | **Erased every epoch** |
| 1e | `federation/src/solo.rs:91` | A nullifier+turn in solo mode | Solo seq | Signed log; rejoiners verify | Append-only signed |
| 1f-cred | `chain/src/credential.rs:226` | (credential serial, action domain) | Credential holder | `presentation_nullifier` field in `CredentialProof` | Per-action-domain |
| 1f-wd | `chain/src/withdraw.rs:178` | Withdrawal note (parallel/alt definition) | Holder | `derive_nullifier` (different domain string!) | Unclear; may be dead code |
| 1f-tok | `token/src/revocation.rs:578` | A token ID | Issuer | `RevocationRegistry::is_revoked` | Append-only with attested Merkle root |
| 1f-cp | `types/src/lib.rs:207` | Top-level commit to set root | Consensus | Checkpoint field | None populates it in prod |

11+ kinds. The `Nullifier` type from `cell/src/note.rs` is used by 1a, 1b, and
1b'; everything else is `[u8; 32]` or a different newtype. There is no
single trait or interface that unifies them.

---

## 10. Open questions for designer

1. **Where is the production wiring for `NullifierSet`?**
   `record_note_spend` in the journal looks finished; no consumer exists.
   Was this intentionally deferred ("note layer" TBD) or accidentally
   dropped? If deferred, what's the planned commit point — at journal-apply
   in `executor.rs`, or in a separate post-commit notes service?

2. **What is the AIR's *actual* binding for `destination_federation`?**
   `note_bridge.rs:1233` carries a `TODO: Ensure NoteSpendingAir includes value
   and asset_type in public inputs` that was clearly partly addressed
   (value/asset_type ARE in the PI now), but `destination_federation` was
   missed. Should `pi` in `note_spending_air.rs` and `dsl/note_spending.rs`
   gain a `DESTINATION_FEDERATION` slot, with a corresponding witness column
   and boundary?

3. **How does the verifier slice the 80-byte / 112-byte PI buffer?**
   (§7.) A spot-check of `wire/src/server.rs`'s `ProofVerifier` impl
   against what `pyana_circuit::stark::verify` expects would resolve this.

4. **`chain/src/withdraw.rs` vs `cell/src/note.rs` — two note nullifier
   derivations.** They use different domain strings (`"pyana-nullifier-v1"`
   vs `"pyana-note nullifier v1"`) and different inputs
   (`(nullifier_key, commitment)` vs `(commitment, spending_key, creation_nonce)`).
   Is `chain/src/withdraw.rs` dead, parallel-design code, or active? If
   active, the two flavours can never be cross-verified.

5. **Should bearer caps be nullifier-shaped or not?** The doc-stated
   ancestry (biscuit/macaroon) says no, but `BearerProof.revocation_channel`
   (turn/src/tests.rs:8376) is operating in a halfway state — revocable but
   not consumable. If the design is "no nullifier, only expiry + channel,"
   the documentation should say so loudly because the rest of the system
   uses "nullifier" prolifically. If the design is "nullifier-shaped per use,"
   the presentation-nullifier in `chain/src/credential.rs` is the right
   primitive and should be wired into `BearerProof`.

6. **Is the stake-nullifier set erasure (`gossip.rs:303`) sound w.r.t.
   replay across epoch boundaries?** A note used 5×in epoch K can be used 5×
   in epoch K+1. That seems intended ("rate-limit per epoch"), but it means
   the stake-nullifier set is **not** a double-spend gate; it's a Sybil
   throttle. Audit reviewers should know this isn't a permanent record.

7. **`Checkpoint.nullifier_set_root: Option<[u8; 32]>`** — when is `Some`
   vs `None` produced? If always None (because nothing writes to a
   persistent set), the field's there for a future protocol upgrade and
   should be documented as such; otherwise external verifiers will assume
   it reflects current spent-state.

---

## 11. Should pyana have nullifiers? Recommendation.

It already does, abundantly. The recommendation is **consolidation and
completion**, not introduction:

1. **Pick one canonical "spent note" set per federation** and wire
   `JournalEntry::NoteSpend` into it on commit. Either `NullifierSet` (in
   memory) or `PersistentNullifierSet` (redb), depending on persistence
   stance. The hook point is `executor.rs:8040-8055` (currently a
   no-op match arm) plus the rollback path in `journal.rs:440-451`. The
   redb path already exists (`store/src/lib.rs:578-614`); use it.

2. **Add `DESTINATION_FEDERATION` as a public input** in both
   `note_spending_air.rs` and `dsl/note_spending.rs`, with a witness column
   and a boundary constraint (`note_spending_air.rs:471-512` is the obvious
   model). Otherwise §5's documentation is materially misleading.

3. **Stop using the word "nullifier" for `compute_proof_hash`.** It is a
   *replay nonce* over a publicly-derivable proof hash. Calling it a
   nullifier conflates it with the Zcash-shape primitive, which has very
   different security/privacy semantics. Suggested rename:
   `compute_proof_replay_token` (the conditional/discharge subsystem only).

4. **Decide on bearer-cap consumability.** Either embrace the
   biscuit/macaroon model (and remove `revocation_channel` from `BearerProof`
   in favour of pure expiry + caveat attenuation), or add a presentation-
   nullifier so that bearer caps with `single_use: true` are enforced.

5. **Resolve the `chain/src/withdraw.rs` parallel definition** — either
   delete it, or document it as a distinct design (withdrawal-shielded vs
   note-shielded). The current state (two nullifier derivations differing in
   domain string) is a footgun.

6. **Bind raw `[u8; 32]` nullifier ↔ in-circuit BabyBear PI explicitly.**
   At minimum, add an integration test that constructs a `NoteSpend` effect,
   runs it through the executor + real STARK verifier, and confirms that the
   verifier *rejects* the same effect submitted with a different bridge
   destination, a different value, and a different asset_type. (§7's
   ambiguity is the biggest single audit-finding here; it would take ~50 lines
   of test to resolve and would either close the trapdoor or surface
   whichever of the three failure modes is real.)
