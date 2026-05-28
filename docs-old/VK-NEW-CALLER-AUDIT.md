# VerificationKey::new / from_parts Caller Audit
## Issue #105 — Should `VerificationKey::new` use `canonical_vk_v2`?

Audit date: 2026-05-25  
Auditor: read-only static analysis, no cargo, local tree only  
Scope: all callers of `VerificationKey::new`, `::from_parts`, `::from_parts_checked`

---

## §1 Caller Table

### VerificationKey::new (16 call sites total)

| # | File:Line | What bytes it passes | Classification |
|---|-----------|----------------------|----------------|
| 1 | `tests/src/adversarial_pipeline.rs:790` | `vk_data` = `*blake3::hash(b"verification-key-data").as_bytes()` — a 32-byte BLAKE3 digest stored as the payload | OPAQUE FIXTURE: the bytes are a deliberate test sentinel; no AIR/verifier/proving-system context is available |
| 2 | `turn/tests/integration_vk_integrity.rs:115` | `b"honest-vk-data"` — a string literal | OPAQUE FIXTURE: integrity smoke test — proves `new` sets `hash == blake3(data)`; no real circuit |
| 3 | `turn/src/tests.rs:265` | `vec![1, 2, 3, 4]` — stub bytes | OPAQUE FIXTURE: proof-permission routing tests; bytes are irrelevant — only the *presence* of a VK matters |
| 4 | `turn/src/tests.rs:314` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 5 | `turn/src/tests.rs:356` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 6 | `turn/src/tests.rs:403` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 7 | `turn/src/tests.rs:2276` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 8 | `turn/src/tests.rs:3778` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 9 | `turn/src/tests.rs:3828` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 10 | `turn/src/tests.rs:3890` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 11 | `turn/src/tests.rs:3951` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 12 | `turn/src/tests.rs:4045` | `vec![1, 2, 3, 4]` | OPAQUE FIXTURE (same as #3) |
| 13 | `cell/src/commitment.rs:524` | `b"new-vk"` — string literal | OPAQUE FIXTURE: adversarial commitment test verifying that changing a VK propagates through the cell commitment; no circuit semantics |
| 14 | `cell/src/tests.rs:459` | `vec![1, 2, 3, 4, 5]` | OPAQUE FIXTURE: unit test for hash computation only |
| 15 | `cell/src/tests.rs:1385` | `vec![0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x02, 0x03]` | OPAQUE FIXTURE: scenario test for zkApp permissions; bytes are arbitrary, no circuit |
| 16 | `demo-agent/examples/programmable_cell.rs:228` | `b"proof-circuit-vk-data-v1"` — string literal | OPAQUE FIXTURE: mock proof-verifier demo; the `MockStarkVerifier` uses whatever bytes are passed — not a real circuit VK |

**Summary: all 16 `VerificationKey::new` call sites pass opaque/synthetic bytes with no AIR fingerprint, verifier fingerprint, or proving-system context available.**

---

### VerificationKey::from_parts (8 call sites)

| # | File:Line | What bytes it passes | What hash it passes | Classification |
|---|-----------|----------------------|---------------------|----------------|
| 17 | `tests/src/fully_private_e2e.rs:254` | `executor_fed_root_bytes` — BabyBear-encoded Poseidon2 federation root (4 bytes from `bb_to_bytes`) | `blake3::hash(&executor_fed_root_bytes)` — recomputed | OPAQUE FIXTURE: uses federation root as VK; bytes are a STARK witness value, not a CellProgram/AIR combo |
| 18 | `tests/src/integration.rs:121` | `vk_bytes` — `[0u8; 32]` with first 4 bytes = `federation_root.0.to_le_bytes()` | `blake3::hash(&vk_bytes)` — recomputed | OPAQUE FIXTURE: same pattern; federation root is wire-proof-level data, no structured components |
| 19 | `tests/src/integration.rs:245` | same `vk_bytes` as #18 | same | OPAQUE FIXTURE (fail-closed test variant) |
| 20 | `tests/src/integration.rs:319` | `wrong_vk_bytes` — deliberate wrong federation root (`99999u32`) | `blake3::hash(&wrong_vk_bytes)` — recomputed | OPAQUE FIXTURE: adversarial wrong-VK test |
| 21 | `turn/tests/integration_vk_integrity.rs:83` | `b"unrelated-vk-data"` — string literal | `[0xAA; 32]` — deliberately wrong, to forge | OPAQUE FIXTURE: integrity test for P0 #69; intentionally forged |
| 22 | `turn/src/executor/apply.rs:2984` | `vk_hash.to_vec()` — the hash itself used as the data payload ("hash IS the identifier") | `*vk_hash` — the same value | CAN DERIVE (borderline OPAQUE): the `effective_vk` is a `[u8; 32]` produced either by `canonical_program_vk_v2` / `ChildVkStrategy::Derived` / `ChildVkStrategy::Fixed`. The 4 components *were* used upstream to compute `vk_hash`, but by the time `from_parts` is called they are not in scope. The data field is intentionally set to the hash itself as a self-referential sentinel. |
| 23 | `cell/src/tests.rs:469` | `vec![10, 20, 30]` | `[0xAA; 32]` — arbitrary pre-computed constant | OPAQUE FIXTURE: unit test for `from_parts` constructor, no semantics |
| 24 | `demo-agent/src/main.rs:238` | `federation_root_bytes` — BLAKE3 hash of a root key bytes slice | `blake3::hash(&federation_root_bytes)` — recomputed | OPAQUE FIXTURE: demo uses federation root as the VK identifier; not a CellProgram VK |

---

### VerificationKey::from_parts_checked (2 call sites, plus definition)

| # | File:Line | What bytes it passes | Classification |
|---|-----------|----------------------|----------------|
| 25 | `turn/tests/integration_vk_integrity.rs:147` | `b"some-vk-data"` with correct hash | OPAQUE FIXTURE: audit test for the integrity check itself |
| 26 | `turn/tests/integration_vk_integrity.rs:150` | same data with bad hash `[0u8; 32]` | OPAQUE FIXTURE: negative test |

Note: `from_parts_checked` is the *correct* constructor for untrusted input paths per the P0 #69 audit note in `cell/src/cell.rs:60-68`. Neither call site above is a production path.

---

### Callers by Classification

| Classification | Count | Sites |
|----------------|-------|-------|
| OPAQUE FIXTURE | 24 | #1–#21, #23–#26 |
| CAN DERIVE (borderline) | 1 | #22 (`apply.rs:2984`) |
| HAS 4 COMPONENTS | 0 | — |

**No caller currently has all four `canonical_vk_v2` components in hand at the call site of `VerificationKey::new` or `from_parts`.**

---

## §2 Recommendation

### Option A — Add `VerificationKey::from_components` constructor that calls `canonical_vk_v2`; deprecate `new`

`from_components` would accept `VkComponents<'_>`, call `canonical_vk_v2` to compute the hash, and store the canonical bytes as the `data` field (or a structured serialization thereof). `new` would be soft-deprecated with a `#[deprecated]` attribute.

**Pros**: hash is guaranteed canonical everywhere the 4 components exist; closes the structural gap raised in #105.  
**Cons**: requires structural changes at all production call sites — but since *every* existing `new` caller is a test/demo fixture with opaque bytes, the migration set for production paths is just one site (#22 in `apply.rs`), and that site is already the tricky one (see §3).

### Option B — Force `VerificationKey::new` to compute `canonical_vk_v2` from the opaque bytes

`new(data)` would fabricate synthetic `VkComponents` — treating `data` as `program_bytes` and using a placeholder AIR fingerprint, verifier fingerprint, and proving-system identifier (e.g., zeros or a "legacy" sentinel). The resulting hash would be consistently computed but would *not* match any real proving-system identity.

**Pros**: no API change for callers.  
**Cons**: mechanically invalid — the hash would commit to "program_bytes = arbitrary opaque bytes" and "AIR = zero sentinel", which is not what any real prover produces. This would make test VKs produce hashes with domain-string `"dregg-vk-v2"` but nonsense semantics. Validators that cross-check VK hashes against real circuit parameters would reject correctly-generated VKs if they were ever constructed this way. The current tests would need their expected-hash values updated or their assertions would silently pass against synthetic values. Net result: Option B is a soundness regression dressed as a fix.

### Option C — Leave `VerificationKey::new` as-is (BLAKE3 of raw data); accept non-canonical hashes for now

**Pros**: zero risk of behavior change; test fixtures continue to work.  
**Cons**: the hash in a `VerificationKey` constructed by `new` is `blake3(data)`, not `canonical_vk_v2(4 components)`. If callers treat the `hash` field as a canonical VK identifier for proof verification, they get a non-interoperable value.

### Verdict: Option A

**Recommended: Option A** — add `from_components` + soft-deprecate `new`.

Justification: the four-component structure is already in place and used by `app-framework/src/vk.rs` for all real cell-program VKs. The only production constructor that is not a test fixture (`apply.rs:2984`) uses a `[u8; 32]` that was itself computed by `canonical_vk_v2` somewhere upstream; its `from_parts` call already stores `vk_hash.to_vec()` as data with `vk_hash` as the hash, which is a self-consistent but not four-component encoding. Option A gives that path a proper upgrade path. Option B is unsound; Option C accepts the status quo indefinitely.

---

## §3 Migration Plan (Option A)

### Phase 1 — Add the new constructor (no callers changed yet)

Add `VerificationKey::from_components(components: &VkComponents<'_>) -> Self` to `cell/src/cell.rs`:

```rust
pub fn from_components(components: &crate::vk_v2::VkComponents<'_>) -> Self {
    let hash = crate::vk_v2::canonical_vk_v2(components);
    // Store the canonical serialization of all four fields as `data`
    // so the data field is recoverable for cross-checking.
    // Alternatively, store the program_bytes only and leave AIR/verifier/psid
    // out-of-band (documented in VkComponents). Decision for implementer.
    let data = components.program_bytes.to_vec();
    VerificationKey { hash, data }
}
```

Add `#[deprecated(since = "...", note = "Use VerificationKey::from_components for production VKs")]` to `VerificationKey::new`. Keep `new` live for test/fixture use.

### Phase 2 — Migrate the one production call site

**`turn/src/executor/apply.rs:2984`** — this is the factory cell-instantiation path. The `effective_vk` value is already the output of `canonical_program_vk_v2` (via `app-framework` or `ChildVkStrategy::Derived`). The workaround is either:

(a) Thread `VkComponents` through `FactoryCreationParams` so `apply.rs` can call `from_components` directly, or  
(b) Accept that the `hash-as-data` sentinel (`vk_hash.to_vec()`) is intentional for factory-created cells — these cells store a derived VK identifier, not raw program bytes. In this case, the existing `from_parts(vk_hash, vk_hash.to_vec())` is correct for its purpose (the hash IS the identifier; there are no raw program bytes to store) and should be left as-is with an explanatory comment. This path should NOT migrate to `from_components`.

**Recommendation for #22**: leave as-is with an explicit comment explaining the "hash-as-identifier" pattern. Add a `// FACTORY-VK: hash IS the identifier; data = hash for self-reference` comment to suppress future confusion.

### Phase 3 — Migrate test fixtures (optional, low priority)

The 24 fixture call sites in `tests/`, `turn/src/tests.rs`, `cell/src/tests.rs`, `cell/src/commitment.rs`, and `demo-agent/` use `new` correctly for their purpose (opaque bytes, no real circuit). They do not need to change. If `new` gains a deprecation attribute, these sites can use a `#[allow(deprecated)]` annotation or be migrated to a test-only helper `VerificationKey::new_for_test(data)` that calls the old implementation without the deprecation warning.

### Migration Order

1. Add `from_components` to `cell/src/cell.rs` (no breaking changes).
2. Soft-deprecate `new` in `cell/src/cell.rs`.
3. Add the `FACTORY-VK` comment at `apply.rs:2984`.
4. Update `app-framework` docs/examples to point to `from_components` for new app VK constructors.
5. Add `#[allow(deprecated)]` to test files or create `new_for_test` alias.

---

## §4 Soundness Implication

### Current state

`VerificationKey::new(data)` computes `hash = blake3(data)`. It does **not** use the `"dregg-vk-v2"` domain key. Therefore, any VK created via `new` has a `hash` that is:

- Consistent internally (`blake3(data)` matches the data).
- **Not** a `canonical_vk_v2` hash for any real proving system.
- **Not** in the `"dregg-vk-v2"` domain.

The cell commitment scheme (`cell/src/commitment.rs`) binds the `hash` field into the cell's content address. So what is committed is `blake3(data)`, not `canonical_vk_v2(4 components)`.

### Is this exploitable?

**In production paths: No, today.** All production VK construction goes through `app-framework/src/vk.rs::canonical_program_vk` → `canonical_vk_v2`. The `VerificationKey` struct in a real production cell will have `hash = canonical_vk_v2(...)` because the hash is set directly from the return value (stored as `child_program_vk: [u8; 32]`), and the `VerificationKey` is constructed via `from_parts(vk_hash, vk_hash.to_vec())` at `apply.rs:2984` — not `new`.

**Structural gap, not an exploit today.** If a caller used `VerificationKey::new(canonical_vk_v2(components).to_vec())` they would get `hash = blake3(canonical_vk_v2_output)` — a double-hash that does not match what a verifier would compute independently. This is the core of #105's concern: a downstream verifier that re-derives the expected VK hash using `canonical_vk_v2` and then compares to `cell.verification_key.hash` would get a mismatch.

However, the existing tests and verifier integration tests all operate consistently: `verifier/tests/integration_forged_proofs.rs` and `verifier/tests/integration.rs` use `EFFECT_VM_VK_HASH_HEX` (the canonical v2 hash) and test that it is accepted. These tests do not go through `VerificationKey::new`; they test the standalone verifier binary's VK resolution, which uses `canonical_vk_v2` directly.

**Concrete exploit scenario**: An attacker cannot today leverage `VerificationKey::new` to forge a proof, because:
1. The proof verifier (`StarkProofVerifier`, `BindingProofVerifier`) receives the VK `hash` and independently derives what the expected VK hash should be from the circuit parameters — if the cell's stored `hash` was set via `new(arbitrary_bytes)`, the verifier's re-derived hash will not match, and the proof will be rejected.
2. `SetVerificationKey` effects go through the `apply` path which calls `from_parts_checked` (per audit P0 #69), enforcing `hash == blake3(data)`. An attacker cannot install a VK with `hash != blake3(data)` via a turn.

**Residual risk**: The gap is not exploitable today because no production VK reaches a cell via `VerificationKey::new`. It would become exploitable if a future code path:
(a) constructs a VK using `new` with bytes that happen to be the raw serialization of a valid proof, and
(b) a downstream verifier trusts the `hash` field to encode `canonical_vk_v2` semantics without re-deriving.

This is a "latent unsoundness" rather than an active exploit. The fix is straightforward (Option A) and has no urgency from an immediate security standpoint — but should be done before any new VK construction paths are added that might inadvertently use `new` in production.

### Bottom line

The current state means any cell that would be constructed internally using `VerificationKey::new` would carry a non-canonical hash — but today **no production code path does this**. The `from_parts(vk_hash, vk_hash.to_vec())` pattern at `apply.rs:2984` is self-consistent in a different way (hash-as-identifier), also non-canonical in the v2 sense, and also not exploitable today. There is no forge opportunity in the live tree.
