# `apply_effect` Decomposition — Observations

These are things noticed while extracting per-`Effect` `apply_*` methods from
the single 3500-LOC `match` block in `turn/src/executor/apply.rs`. **None were
fixed by the refactor** (the refactor is behavior-preserving by contract). Each
is a candidate for follow-up triage.

## Possible sharp edges

### 1. `NoteSpend` ignores `value_commitment`

```rust
Effect::NoteSpend {
    nullifier, note_tree_root, spending_proof, value, asset_type,
    ..  // value_commitment dropped here
} => { ... }
```

The `value_commitment: Option<[u8; 32]>` field is silently ignored at the
executor's apply site. If a turn supplies a `value_commitment`, the executor
neither verifies nor records it; nullifier-set insertion and balance accounting
go through `value` / `asset_type` regardless. The doc comment on the type says
"the executor uses the committed conservation path instead of cleartext value
comparison" when present — but `apply_effect` does NOT branch on
`value_commitment.is_some()`. Either the committed path is wired elsewhere
(possibly the higher-level conservation check) and this is fine, or the
documented behavior is not implemented at the apply layer.

### 2. `NoteCreate` ignores everything except `commitment`

```rust
Effect::NoteCreate { commitment, .. } => { ... }
```

The variant has six fields (`commitment, value, asset_type, encrypted_note,
value_commitment, range_proof`) and the apply path uses only `commitment` for a
non-zero check and journaling. Same comment as `NoteSpend` — conservation
binding presumably lives at a different layer, but the apply site is silent
about it.

### 3. `ExerciseViaCapability` permission projection only catches `from ==
cap_target` transfers

In the inner-effects permission projection:

```rust
Effect::Transfer { from, .. } if from == &cap_target => Some((Action::Send, "Send")),
```

A `Transfer { from: <not-cap-target>, .. }` inside `inner_effects` skips the
target-cell permission gate entirely. The capability's target cell permissions
are NOT checked against the inner transfer in that case. This may be
intentional (the inner transfer is then governed by *its* `from` cell's
permissions through a recursive `apply_effect`), but the asymmetry is a
foot-gun: an `ExerciseViaCapability` whose inner effect sends FROM a
*different* cell that the actor also has access to silently bypasses the
exercised capability's facet without warning.

### 4. `QueueEnqueue` has no per-queue ACL — anyone with budget can enqueue

`apply_queue_enqueue` checks only:

- queue exists,
- queue is not full,
- actor has `deposit` balance.

There is no capability check, no allowlist, no `Send` permission gate on the
queue cell. Queue cells are created with fully-open `Permissions` in
`apply_queue_allocate`, which is consistent — but the consequence is that
*any* actor on the federation can fill anyone else's queue up to its capacity,
draining their dequeue slots without consent. This is fine for "public mailbox"
queues but there's no opt-in for "private/restricted" ones.

### 5. `QueuePipelineStep` does not check sink ownership

```rust
Effect::QueuePipelineStep { ... source, sinks } => {
    // owner check on source only:
    if source_owner != *action_target.as_bytes() { return Err(...); }
    // sinks: only capacity check, NO ownership check
    for sink in sinks { /* checks sink_capacity, no owner */ }
}
```

A pipeline step requires `action_target` to own the source queue, but the
sinks can be ANY queue cells. Combined with #4 (open enqueue), a malicious
actor who owns one queue can fan-out into any victim's queues by listing them
as sinks. Same "public mailbox" rationale would apply, but it's now coupled to
the source-queue owner's identity in the receipt path.

### 6. `CreateObligation` ignores the `condition` field

```rust
Effect::CreateObligation {
    beneficiary, condition: _, deadline_height, stake, stake_amount,
} => { ... }
```

The `condition: ProofCondition` is destructured and bound to `_`. The apply
site neither validates the condition's well-formedness, hashes it into the
`obligation_id`, nor records it in the `ObligationRecord` (which has no
`condition` field). At fulfillment, the executor doesn't know what condition
the obligation was created against — it accepts any `StarkProof` whose verifier
succeeds against `"obligation-fulfill"`/`"obligation"` keyed by
`obligation_id`. If the verifier doesn't intrinsically depend on the condition
(it appears not to), the obligation can be fulfilled by any proof that
satisfies the generic obligation-fulfill verifier — the *type* of obligation
isn't pinned by the on-chain record. The `stake` commitment IS hashed into
`obligation_id`, so condition identity could go there too — but currently it
doesn't.

### 7. `FulfillObligation` "fail-open" when no verifier configured

```rust
if let Some(verifier) = &self.proof_verifier { ... } else {
    // If no verifier configured but proof is provided, that's acceptable
    // (fail-open for the proof, but access control still enforced above).
}
```

The inline comment is explicit about this. Worth flagging: an executor
deployed without a `proof_verifier` will accept obligation fulfillment with
ANY non-empty proof bytes (after the obligor-only access check). The access
check (`action_target == record.obligor`) is the only line of defense in that
configuration. Probably fine in production where a verifier is always
configured, but in test/dev paths this could mask broken proofs.

## Notes that are NOT bugs (just things I had to learn)

- `apply_set_field` invalidates `c.state.commitments[index]` after writing a
  new value — preserved correctly in the extracted method.
- `apply_grant_capability` allows self-grants without c-list lookup (correct,
  documented inline).
- `apply_attenuate_capability` requires `cell == actor` — capabilities are
  attenuated only by the cell that holds them, not their `action_target`. This
  is an exception to the "everything keyed by action_target" pattern, and worth
  noting if anyone adds new attenuation paths.
- `apply_bridge_mint` reaches for `dregg_circuit::dsl::note_spending` directly
  rather than going through the `ProofVerifier` trait — this is documented
  inline as a deliberate fix for a previous truncation bug. Preserved verbatim.
