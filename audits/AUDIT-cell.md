# AUDIT-cell.md

**Scope:** `/Users/ember/dev/breadstuffs/cell/src/` (lib.rs, id.rs, state.rs, cell.rs, capability.rs, delegation.rs, facet.rs, ledger.rs, program.rs, permissions.rs, factory.rs, seal.rs).
**Method:** Read of all listed files, cross-reference with `circuit/src/effect_vm.rs` (commitment side) and `turn/src/executor.rs` (mutation side); cross-reference with `AUDIT-wallet.md` and `AUDIT-sdk-rest.md`.

## Verdict: NEEDS-WORK

The cell crate is functionally rich but has **multiple disjoint "state commitment" definitions** that are never mechanically tied together, **wholly public mutable state** on every authority-bearing struct, and **no enforcement** for the privacy/sealing fields that the type system pretends to model. The wallet's sealed-value discipline is **completely absent** here. The runtime works because the executor is the only mutator in practice — but that's an unenforced convention, not a structural property of the types.

## Summary

`CellState` (in `state.rs`) is a plain `pub struct` with eight `pub` fields including `nonce`, `balance`, `fields`, `proved_state`, `delegation_epoch`, and the visibility/commitment arrays. Every field is freely mutable from any holder of `&mut CellState`, and the struct can be constructed field-by-field with `CellState { ... }` — bypassing `new()`, `set_field()`, `set_field_visibility()`, `apply_balance_change()`, and `increment_nonce()`. The same is true of `Cell` (in `cell.rs`): `id`, `public_key`, `state`, `permissions`, `verification_key`, `delegate`, `delegation`, `token_id`, `capabilities`, `program`, and `mode` are all `pub`. The content-addressed `id` is *derived* from `(public_key, token_id)` at construction, but a holder of `&mut Cell` can replace `id` without touching the pubkey/token_id and break the content-address invariant. Compare to `wallet::HeldToken`, whose sealed-value pattern *prevents* such mutations at compile time.

`CellState::compute_commitment` (private, in `state.rs`) is a per-field BLAKE3 commitment — nothing like the cell-level state commitment. `Cell::state_commitment()` (BLAKE3) and `Ledger::hash_cell()` (BLAKE3) and `circuit::CellState::compute_commitment()` (Poseidon2 over BabyBear) are **three different hash schemes over three different field selections** with no shared code or test that they agree. The sovereign-cell path uses `Cell::state_commitment()` only; the Merkle ledger uses `hash_cell()`; the STARK uses Poseidon2. There is no point in the codebase where a single piece of state is hashed by both BLAKE3 and Poseidon2 and the two are equated; the trust gap is bridged only by the federation choosing to believe one or the other for a given query.

`sealed_field_mask` and `mode_flag` appear *only* in the circuit's `CellState` (`circuit/src/effect_vm.rs:632-635`); the cell crate's `CellState` does not carry them at all. The cell-side `FieldVisibility` enum exists, but **the executor does not consult it** when applying field updates (no grep hits in `turn/src/executor.rs`); the executor freely overwrites committed fields without re-committing. `proved_state` is honored by the executor.

## Findings

### P0 (critical)

**P0-1. Public-mutable `CellState` and `Cell` — no construction discipline.**
`cell/src/state.rs:36-57` and `cell/src/cell.rs:50-81`: every authority-bearing field is `pub`. A holder of `&mut Cell` can (a) set `cell.state.balance = u64::MAX` without going through `apply_balance_change`, (b) rewrite `cell.id` to point to a different content-address than `(public_key, token_id)` would derive, (c) decrement `cell.state.nonce` to enable replay, (d) overwrite `cell.permissions` and `cell.verification_key` directly, (e) replace `cell.state.fields[i]` while leaving the stale `commitments[i]` in place. The wallet's `HeldToken` adopts the explicit sealed-value pattern for exactly this reason. The same discipline should apply here: `Cell` and `CellState` should expose only read accessors plus controlled mutators (`apply_delta`, `increment_nonce`, etc.) and force callers to go through them. Today the `Ledger` API gives out `get_mut(&mut Cell)` (`ledger.rs:310`), so any `&mut Ledger` holder gets the full footgun.

**P0-2. Three independent state-commitment schemes, no cross-check.**
- `Cell::state_commitment()` (`cell/src/cell.rs:239-288`) hashes `id || public_key || token_id || nonce || balance || fields || cap_count || (target,slot)* || perms_bytes || vk_flag || vk_hash` using BLAKE3 (`pyana-cell-state-v1`). Notably **omits**: `field_visibility`, `commitments`, `proved_state`, `delegation_epoch`, `delegate`, `delegation`, `program`. Used by sovereign cell witness verification (`turn/src/executor.rs:1770`).
- `Ledger::hash_cell()` (`cell/src/ledger.rs:814-973`) hashes a *superset*: everything in `state_commitment()` plus `field_visibility`, `commitments`, `proved_state`, `delegation_epoch`, `program`, `delegate`, and a (lossy) `delegation` digest. Used as the leaf hash in the federation Merkle tree.
- `circuit::CellState::compute_commitment()` (`circuit/src/effect_vm.rs:668-679`) hashes only `(split_u64(balance), nonce, fields[0..8], capability_root)` with Poseidon2 over BabyBear in a fixed tree shape. Omits ID, pubkey, token_id, permissions, vk, visibility, delegation, program.
A sovereign cell's identity in the circuit therefore has **no binding** to its permissions or verification key. Two cells with identical `(balance, nonce, fields, cap_root)` but completely different `Permissions` produce the same circuit-side commitment. The executor checks `state_commitment` against the stored sovereign commitment (executor.rs:1782), and separately the STARK proves a Poseidon2 commitment transition — but **nothing checks that the Poseidon2 commitment corresponds to the BLAKE3-state-commitment for the same `Cell`**. A prover that controls a sovereign cell and produces an honest Poseidon2 proof over `(balance, nonce, fields, cap_root)` does not prove anything about its permissions or VK; an attacker who can plausibly construct a witness with matching `(balance, nonce, fields, cap_root)` but altered permissions has a path to ledger-acceptance under the right call order. This is the type-layer manifestation of the "different `CellState`s in different worlds" gap.

**P0-3. `capability_root` is undefined in the cell crate.**
The circuit commits to `capability_root: BabyBear`. The cell crate has `CapabilitySet` but **never computes a Merkle/Poseidon2 root** over it, and `Cell::state_commitment()` does not produce one either (it concatenates `(target, slot)` pairs into a BLAKE3 stream). There is no function in `cell/src/capability.rs` that produces a `capability_root` value matching what the circuit expects. So `capability_root` in the circuit is effectively a witness with no constraint binding it to the actual c-list — anyone producing a STARK gets to choose it, and the system has no way to detect this mismatch.

### P1 (high)

**P1-1. `CellId` is `pub [u8; 32]` and `from_bytes` is unrestricted.**
`types/src/lib.rs:406`, `:435`: `CellId(pub [u8; 32])` and `pub fn from_bytes(bytes: [u8; 32]) -> Self` mean any caller can mint a CellId with an arbitrary value, bypassing content-addressing. Combined with P0-1 (mutable `cell.id`), this means CellId provenance is purely social. Used in `seal::deserialize_capability` (`cell/src/seal.rs:340`) where attacker-controlled bytes flow directly into a `CellId`. Recommend: keep `from_bytes` for deserialization but make `CellId::0` private and add a `derive_or_decode` boundary.

**P1-2. `set_field` silently invalidates commitments without warning callers.**
`state.rs:144-155`: on a field write, if `commitments[index].is_some()`, it gets nulled to `None`. Subsequently calling `get_field_public(index)` for a `Committed`/`SelectivelyDisclosable` field returns `PublicFieldView::Revealed(self.fields[index])` (`state.rs:125-129`) — i.e. the supposedly-private value leaks. The visibility flag is preserved but the commitment is gone, and the public-view function silently falls through to "show the plaintext." Per the contract, this means: anyone with read access to the cell state after a field-set sees the supposedly-private value until the holder re-commits. The executor never re-commits, so any "committed" field written via `Effect::SetField` is effectively public. The `FieldVisibility` enum is aspirational naming.

**P1-3. `field_visibility` is unenforced by the executor.**
No grep hit for `field_visibility` or `FieldVisibility` in `turn/src/executor.rs`. The executor neither rejects writes to `Committed` fields without a fresh commitment nor masks reads. As the wallet audit calls this category: "names without teeth." If the cell model is supposed to provide progressive disclosure, the executor (and the ledger leaf-hash function) need to enforce that public observers cannot read `Committed` slot values. Currently `Ledger::hash_cell` includes the full `fields` array in the leaf hash regardless of visibility (`ledger.rs:825-827`), so any party with the Merkle proof + leaf preimage learns the field.

**P1-4. `serde` deserialization of `CellState` / `Cell` is unbounded.**
`CellState` is `#[derive(Deserialize)]` with no size limits. `[FieldElement; STATE_SLOTS]` is a fixed-size array (OK), but `delegation.snapshot: Vec<CapabilityRef>`, `Permissions` (8 enum bytes — fine), and the `Cell::verification_key.data: Vec<u8>` are unbounded. An attacker who can submit a `Cell` or `DelegatedRef` via any deserializing entry point (`apply_delta`, peer-exchange, persistence checkpoints) can balloon memory with `Vec<u8>` and `Vec<CapabilityRef>`. Similar concern flagged in AUDIT-wallet for `postcard`/`rmp-serde` paths.

**P1-5. `Cell::spawn_child_with_delegation` produces a placeholder signature.**
`cell/src/cell.rs:341`: `[0u8; 64], // Placeholder signature — spawn_child is a privileged internal op.` The `DelegatedRef::verify_parent_signature` will refuse this (Ed25519 reject of all-zero), but the `parent_signature` field is `pub` (mutable post-construction) and the comment claims "privileged internal op" without actually being gated. If `spawn_child_with_delegation` is exposed to any operation reachable via the executor (it is — `cell.rs:312` is `pub fn`), the caller can mint a forged delegation by calling this, then never run the signature verifier. Verifier-side discipline only protects acceptors who actually call `verify_parent_signature`. Default: trust nothing without verifying.

**P1-6. `Ledger` is `Clone` with no encapsulation.**
`ledger.rs:260`: `#[derive(Clone, Debug)] pub struct Ledger { cells: HashMap<CellId, Cell>, ... }`. Fields are private, which is good. But `get_mut` returns `&mut Cell`, exposing P0-1's surface. Also `dirty: bool` is private but tied to mutation; any operation that mutates a `Cell` reference must mark dirty — the borrow exposes the cell with no enforced "dirty" callback. Recommend: replace `get_mut` with `update_with(id, |c| {...})` that automatically sets dirty.

### P2 (medium)

**P2-1. `is_effect_permitted(Some(0), ...) => true`.**
`facet.rs:91-96`: `Some(0) => true, // zero mask = unrestricted (backward compat)`. An attacker who can construct a faceted capability with `allowed_effects: Some(0)` gets an *unrestricted* capability with the appearance of being heavily faceted. The intuitive reading is "zero mask = deny all." Recommend either (a) `Some(0) => false` and migrate any "I want unrestricted" callers to `None`, or (b) reject zero masks at construction time.

**P2-2. `wrapping_add` on nonce.**
`state.rs:159`: `self.nonce = self.nonce.wrapping_add(1);` and `:185`: `delegation_epoch.wrapping_add(1)`. After 2^64 increments these wrap and re-enable replay of historical actions. `wrapping_add` here is wrong choice — `checked_add` and a hard error on overflow is right. Similar with `delegation_epoch.wrapping_add`.

**P2-3. `Cell::id` mutability + content-addressing.**
`cell.rs:53`: `pub id: CellId`. Each constructor recomputes `id = CellId::derive_raw(&public_key, &token_id)`. Nothing maintains the invariant `cell.id == derive_raw(cell.public_key, cell.token_id)` after construction. Anyone mutating `cell.public_key` does not update `cell.id`. The `Ledger` uses `cell.id` as the key in its `HashMap`, so a cell can sit at a key inconsistent with its content. Add a `Cell::verify_id_integrity(&self) -> bool` and check it at every authoritative call site (proof verification, sovereign witness ingest, peer-exchange ingest).

**P2-4. `Ledger::hash_cell` lossy on `delegation.snapshot`.**
`ledger.rs:963-966`: only `(target, slot)` pairs from `snapshot` are hashed; `permissions`, `breadstuff`, `expires_at`, `allowed_effects` are dropped. Two delegated snapshots with the same `(target, slot)` list but completely different permissions hash identically into the Merkle tree, so a Merkle proof binds nothing about the actual delegated permission strength. (The full snapshot is committed elsewhere via `DelegatedRef::clist_commitment`, but the leaf hash should still cover it.)

**P2-5. `Ledger` panics from `.unwrap()` on tree manipulation paths.**
`ledger.rs:392`, `:618`, `:698`, `:743`, `:757`: panics if invariants are violated. Most are protected by prior contains-checks, but in the apply_delta path (`:392`, `new_cells.get_mut(&from_id).unwrap()`), if a duplicate from_id transfer exists in the delta, the second transfer can hit a state the first transfer left in an unexpected shape. Not exploitable from a trusted executor, but DoS-able through unchecked deserialization (see P1-4).

**P2-6. `compute_clist_commitment` does not include `expires_at` / `allowed_effects` validation context.**
`delegation.rs:118-122`: hashes the serialized bytes via postcard. Postcard's encoding is fine, but the *signed* message (`signing_message`, `delegation.rs:128-138`) covers only `(clist_commitment, delegation_epoch, child_cell_id)`. A parent who signs a delegation at epoch N can have that signature replayed against a *different* child at the same epoch if the attacker can craft a clist with the same commitment. Mitigations exist (`child_cell_id` is signed), but the parent's pubkey is not bound into the commitment hash. Recommend including the parent pubkey in `signing_message` derive_key context.

### P3 (low / hygiene)

- `cell.rs:331` and `ledger.rs:921`: `postcard::to_allocvec(&snapshot).unwrap_or_default()` — silently substitutes empty Vec on serialization failure, which then hashes as a real empty commitment. Postcard rarely fails, but a `panic!` would be more honest.
- `nullifier_set.rs`, `revocation_channel.rs`, `derivation.rs`, `facet.rs`, `factory.rs`: large public surfaces, mostly read-only. Not audited in depth for this pass.
- `permissions.rs:163-167`: `Default for Permissions` returns `default_user()` (`Signature` required for everything except `receive`/`access`), but `Cell::new()` and `from_config` both apply this. A new sovereign cell with no further customization permits *signature* mutations, not proof. Consider making sovereign cells default to `sovereign_default()` (`set_verification_key: Proof`) at the `from_config` level.
- `state.rs:78`: `proved_state: false` initial — fine, but `delegation_epoch: 0` is the same default for unrelated cells and any "epoch == 0 means uninitialized" check would be wrong.
- `cell.rs:240`: domain-separated as `pyana-cell-state-v1`, but the field selection diverges from `ledger.rs:815` (`pyana-cell:merkle-leaf v2`). The v1/v2 naming is inconsistent and the diverging field sets are likely to cause future bugs.

## Public API table (selected, authority-bearing)

| Symbol | File:line | Trust class | Notes |
|---|---|---|---|
| `CellState { pub fields, pub nonce, pub balance, pub proved_state, pub commitments, ... }` | state.rs:36 | **Anyone with `&mut`** | P0-1 — should be sealed |
| `CellState::new(balance)` | state.rs:70 | Anyone | Construction; fine |
| `CellState::set_field(index, value)` | state.rs:144 | Anyone with `&mut` | P1-2 — invalidates commitment, no callback |
| `CellState::increment_nonce` | state.rs:158 | Anyone | P2-2 — wrapping_add |
| `CellState::apply_balance_change(delta)` | state.rs:163 | Anyone | OK, checked arithmetic |
| `Cell { pub id, pub public_key, pub state, pub permissions, pub verification_key, pub delegate, pub delegation, pub token_id, pub capabilities, pub program, pub mode }` | cell.rs:50 | **Anyone with `&mut`** | P0-1 — all fields exposed |
| `Cell::state_commitment()` | cell.rs:239 | Anyone, read-only | P0-2 — disjoint from circuit |
| `Cell::spawn_child_with_delegation` | cell.rs:312 | Anyone (since pub) | P1-5 — placeholder signature |
| `CapabilitySet::grant_*` | capability.rs:82-178 | Anyone with `&mut` | OK; checked next_slot overflow |
| `CapabilitySet::revoke(slot)` | capability.rs:181 | Anyone with `&mut` | Atomic, idempotent (returns false if absent) |
| `CapabilitySet::attenuate / attenuate_faceted` | capability.rs:227-275 | Anyone | Correctly enforces narrowing |
| `DelegatedRef::verify_parent_signature` (feature=crypto) | delegation.rs:144 | Anyone, read-only | Correct Ed25519 strict verify |
| `Ledger::get_mut` | ledger.rs:310 | Operator-only by convention | P1-6 — full footgun |
| `Ledger::insert_cell` | ledger.rs:345 | Operator | Rejects duplicate |
| `Ledger::apply_delta` | ledger.rs:357 | Operator | Pre-validation + clone-and-swap (good) |
| `Ledger::make_sovereign` | ledger.rs:1087 | Operator | Used by `Effect::MakeSovereign`; gated in executor |
| `Ledger::register_sovereign_cell_*` | ledger.rs:1048,1106,1118 | Operator | OK |
| `Ledger::update_sovereign_commitment` | ledger.rs:1066 | **Operator** | No "old commitment" check in this variant — variant at :1164 does check |
| `CellId(pub [u8; 32])`, `CellId::from_bytes` | types/lib.rs:406,435 | Anyone | P1-1 — pub tuple field |
| `is_effect_permitted(Some(0), _)` returns `true` | facet.rs:91 | — | P2-1 — counterintuitive |

## Commitment-binding cross-check

The three independent commitment functions (`Cell::state_commitment`, `Ledger::hash_cell`, `circuit::CellState::compute_commitment`) commit to different subsets of state with different hashes:

| Field | `state_commitment` (BLAKE3) | `hash_cell` (BLAKE3) | `circuit::compute_commitment` (Poseidon2) |
|---|---|---|---|
| `id` / `public_key` / `token_id` | yes | yes | no |
| `nonce` | yes | yes | yes |
| `balance` | yes | yes | yes (`split_u64`) |
| `fields[0..8]` | yes | yes | yes |
| `field_visibility` | **no** | yes | no |
| `commitments[0..8]` | **no** | yes | no |
| `proved_state` | **no** | yes | no |
| `delegation_epoch` | **no** | yes | no |
| capabilities | yes (target+slot) | yes (target+slot+perms+breadstuff+expires) | `capability_root` (uncomputed in cell crate — P0-3) |
| `permissions` | yes (each field's variant byte) | yes | **no** |
| `verification_key.hash` | yes | yes | **no** |
| `delegate` / `delegation` | **no** | yes (lossy) | no |
| `program` | **no** | yes | no |
| `sealed_field_mask` / `mode_flag` | n/a (not in cell-side `CellState`) | n/a | yes (witness only) |

**Conclusion:** No two of these three commit to the same thing. The system relies on this gap being unobservable — the federation uses `hash_cell` for the Merkle tree; the sovereign-witness check uses `state_commitment`; the STARK proves Poseidon2 commitments. Nothing in the code joins them. To preserve "the proof binds the state the agent declared," the system needs either (a) a single canonical state-commitment function exported from `cell/` and used by both the sovereign witness check AND the circuit (presumably via a `to_babybear_fields` adapter so the Poseidon2 hash takes the same logical content), or (b) explicit cross-domain binding (e.g., the BabyBear public input is `hash_to_babybear(state_commitment_blake3)`).

## Open questions for the user

1. **Is the sealed-value pattern (per `HeldToken`) supposed to apply to `Cell`/`CellState`?** If yes, this is a P0 refactor to fix P0-1. If "no, because the executor is trusted," then the trust boundary should be documented and the `pub` fields gated behind a `#[cfg(test)]` setter-only API, with non-test mutation going through `Ledger::apply_delta` exclusively.
2. **What is `capability_root` supposed to be?** Is the cell crate supposed to provide a `CapabilitySet::poseidon2_root()` that the circuit consumes? Right now the circuit field has no source (P0-3).
3. **Should `Permissions` and `verification_key` be inside the circuit's `state_commitment`?** Otherwise upgrades to either can be lied about in proofs.
4. **What is the intended semantics of `FieldVisibility::Committed`?** If it is supposed to prevent leaf-hash leakage in the Merkle tree, `hash_cell` must replace `fields[i]` with `commitments[i]` for non-public slots — and `set_field` must re-commit, not invalidate. As written, the privacy claim does not hold.
5. **Is `is_effect_permitted(Some(0), _) => true` intentional?** This is a footgun against the natural reading.
6. **Should the cell crate export the `state_commitment` to the circuit instead of having two implementations?** A `#[cfg(feature = "zkvm")]` adapter that converts `CellState` to the circuit's `CellState` and asserts the BLAKE3 hash equals a known Poseidon2 commitment over the same fields would close P0-2.
