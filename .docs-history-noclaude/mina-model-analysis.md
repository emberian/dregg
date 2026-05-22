# Mina zkApp Transaction Model vs. Pyana Cell/Turn Model

Deep analysis from source code reading of both systems.

---

## 1. Mina's Actual Model (from Source)

### 1.1 The ZkappCommand (Transaction)

A transaction (`Zkapp_command.t`) is:
```
{ fee_payer: Fee_payer.t
; account_updates: Call_forest.t   (* tree of AccountUpdates *)
; memo: Signed_command_memo.t }
```

The **fee payer** is special:
- Always uses the default MINA token
- Always has `Signature` authorization
- Always increments nonce
- Always has `use_full_commitment = true`
- Balance change is always **negative** (the fee amount)
- Its nonce precondition is always exact (replay protection)
- It runs in a "first pass" against a separate ledger snapshot
- **If the fee payer fails, the entire transaction is hard-rejected (not even applied)**

### 1.2 The AccountUpdate (Body)

Each AccountUpdate body contains:

| Field | Semantics |
|-------|-----------|
| `public_key` | Target account's public key |
| `token_id` | Which token domain (default = MINA) |
| `update` | Set-or-Keep for: app_state[8], delegate, verification_key, permissions, zkapp_uri, token_symbol, timing, voting_for |
| `balance_change` | Signed amount (positive = deposit, negative = withdrawal) |
| `increment_nonce` | Whether to bump the account's nonce |
| `events` | Arbitrary field arrays (logged, not stored) |
| `actions` | Arbitrary field arrays (affect action_state rolling hash) |
| `call_data` | Single field element (opaque, committed in hash) |
| `preconditions` | { network: protocol_state, account: Account_precondition, valid_while: slot_range } |
| `use_full_commitment` | If true, signs over memo+fee_payer+all_updates; if false, just over remaining updates |
| `implicit_account_creation_fee` | If true, account creation fee comes from this update's balance change |
| `may_use_token` | No / Parents_own_token / Inherit_from_parent |
| `authorization_kind` | None_given / Signature / Proof(vk_hash) |

The authorization itself is a separate field on the outer `Account_update.t`:
```
{ body: Body.t ; authorization: Control.t }
```
where `Control.t = None_given | Signature sig | Proof proof`.

### 1.3 The Call Forest

The call forest is a **list of trees**. Each tree node has:
- An `account_update` (the action)
- A list of `calls` (child trees)
- An `account_update_digest` (hash of the body)

Hashing: `tree_hash = H(account_update_digest, calls_hash)`, where `calls_hash` is the hash of the child forest (cons-list hash). The forest hash is a right-folded cons hash: `forest_hash = H(tree_hash_0, H(tree_hash_1, ... H(tree_hash_n, empty)))`.

**Traversal order**: The execution logic processes the forest as a **stack machine** (not simple DFS). When an account update is popped:
1. If its `calls` (child forest) is non-empty, push the remaining siblings onto the call stack, then descend into the calls forest.
2. If calls are empty and siblings remain, continue with siblings.
3. If both are empty, pop from the call stack (return to parent's remaining siblings).

This is effectively a pre-order DFS, but implemented as explicit stack manipulation for the SNARK circuit.

### 1.4 Token Ownership and `may_use_token`

Token IDs are derived: `token_id = Account_id.derive_token_id(~owner:account_id)`. An account with `token_id != default` is a "custom token account."

The **critical rule**: If an account update targets a non-default token, the token **owner** must be the caller in the call forest. Specifically:

```
default_token_or_token_owner_was_caller =
  Token_id.equal(account_update_token_id, Token_id.default)
  || Token_id.equal(account_update_token_id, caller_id)
```

Where `caller_id` is determined by `may_use_token`:
- `No` => caller_id = Token_id.default (can only use MINA)
- `Parents_own_token` => caller_id = Token_id derived from the direct parent's account_id
- `Inherit_from_parent` => caller_id = whatever the parent's caller was (transitive)

This is how token owners gate access to their token: child account updates in the forest under a token owner inherit the right to use that token.

### 1.5 The Permission System

13 permission-gated actions, each with an `Auth_required`:
- `edit_state` - modify app_state[8]
- `access` - even read/touch the account
- `send` - negative balance change
- `receive` - positive balance change
- `set_delegate` - change delegate
- `set_permissions` - change permissions themselves
- `set_verification_key` - change vk (also has a `txn_version` for migration)
- `set_zkapp_uri` - change the zkapp URI
- `edit_action_state` - push to action state
- `set_token_symbol` - change token symbol
- `increment_nonce` - bump nonce
- `set_voting_for` - change governance vote
- `set_timing` - change vesting schedule

Auth levels (from source): `None | Either | Proof | Signature | Impossible`

The `check` function:
```
Impossible, _ => false
None, _ => true
Proof, Proof => true
Signature, Signature => true
Either, (Proof | Signature) => true
Signature, Proof => false
Proof, Signature => false
(Proof | Signature | Either), None_given => false
```

**Key insight**: Permissions are checked against the proof/signature status of the CURRENT account update, not some external authority. If you provide a proof matching the cell's vk, you satisfy Proof-level permissions on THAT cell.

### 1.6 Execution Logic (zkapp_command_logic.ml)

The `apply` function processes ONE account update at a time. Order of operations:

1. **Pop next account update** from call forest stack machine
2. **Token owner check**: verify caller_id matches token_id
3. **Get account** from ledger (or create placeholder for new accounts)
4. **Compute transaction commitment** (hash of remaining forest)
5. **Self-delegate**: if new account with default token, set delegate = public_key
6. **Verification key hash check**: if proved, vk_hash must match account's vk
7. **Account precondition check**: balance range, nonce range, field equalities, proved_state, is_new, delegate, receipt_chain_hash, action_state
8. **Protocol state precondition check**: global slot range, blockchain length, etc.
9. **Valid-while check**: current slot must be in valid range
10. **Authorization verification**: check signature or proof against commitment
11. **Fee payer nonce must increase** (only for first update)
12. **Fee payer must be signed** (only for first update)
13. **Replay check**: must either (a) increment nonce with constant precondition, (b) use_full_commitment (depends on fee payer nonce), or (c) not use a signature
14. **Set timing** (permission check: set_timing, only if account is untimed)
15. **Account creation fee**: if new, deduct creation fee from balance_change or from excess
16. **Apply balance change**: add signed amount to balance
17. **Timing validity check**: ensure minimum balance isn't violated
18. **Access permission check**: basic access gate
19. **Update app_state** (permission: edit_state)
20. **Update proved_state**: true if all 8 fields set by proof; false if any set by non-proof; unchanged if fields unchanged
21. **Update verification_key** (permission: set_verification_key)
22. **Update action_state**: push events to rolling hash, shift history if new slot
23. **Update zkapp_uri** (permission: set_zkapp_uri)
24. **Update token_symbol** (permission: set_token_symbol)
25. **Update delegate** (permission: set_delegate, only for default token)
26. **Increment nonce** (permission: increment_nonce)
27. **Update voting_for** (permission: set_voting_for)
28. **Update receipt chain hash**: if auth succeeded
29. **Update permissions** (permission: set_permissions) -- LAST, so current perms gate everything above
30. **Init account** (set public key for new accounts)
31. **Compute local excess delta**: negate(balance_change), accumulate into local excess (only for default token)
32. **Write account back to ledger**
33. **Check fee excess settlement**: at end of transaction, excess must be zero
34. **Update global state**: fee excess, supply increase (only on last update)
35. **Two-pass ledger**: fee payer writes to first_pass_ledger, then all other updates write to second_pass_ledger

**Critical atomicity rule**: The fee payer ALWAYS succeeds (hard assertion). If any other update's checks fail, the failure is tracked in `local_state.success`, and at the end, if `success = false`, the second_pass_ledger is NOT committed (but the fee is still taken from the first_pass_ledger).

### 1.7 Account Preconditions (from zkapp_precondition.ml)

```
Account precondition:
  { balance: Balance range (or Ignore)
  ; nonce: Nonce range (or Ignore)
  ; receipt_chain_hash: exact (or Ignore)
  ; delegate: exact public_key (or Ignore)
  ; state: [8] exact field (or Ignore each)
  ; action_state: exact field (or Ignore)
  ; proved_state: exact bool (or Ignore)
  ; is_new: exact bool (or Ignore) }
```

### 1.8 The `proved_state` Mechanism

Unique Mina innovation. If all 8 app_state fields are set by a proof-authorized update, `proved_state = true`. This guarantees the state was produced by the zkApp's circuit. If any field is modified by a non-proof authorization, `proved_state = false`.

Preconditions can assert `proved_state = true`, ensuring the state they depend on was cryptographically produced.

---

## 2. Pyana's Current Model

### 2.1 Cell (analogous to zkApp Account)

```rust
Cell {
    id: CellId,                        // BLAKE3(public_key || token_id)
    public_key: [u8; 32],
    state: CellState { fields: [FieldElement; 8], nonce: u64, balance: u64 },
    permissions: Permissions { send, receive, set_state, set_permissions,
                              set_verification_key, increment_nonce, delegate, access },
    verification_key: Option<VerificationKey>,
    delegate: Option<CellId>,
    token_id: [u8; 32],
    capabilities: CapabilitySet,       // <-- NOT IN MINA
}
```

### 2.2 Turn (analogous to ZkappCommand)

```rust
Turn {
    agent: CellId,                     // analogous to fee_payer
    nonce: u64,                        // replay protection
    call_forest: CallForest,           // the tree of actions
    fee: u64,                          // in computrons
    memo: Option<String>,
    valid_until: Option<i64>,          // expiration
}
```

### 2.3 Action (analogous to AccountUpdate)

```rust
Action {
    target: CellId,                    // which cell
    method: Symbol,                    // hashed method name (NOT IN MINA)
    args: Vec<FieldElement>,           // arguments (NOT IN MINA as such)
    authorization: Authorization,      // Signature/Proof/Breadstuff/None
    preconditions: Preconditions,
    effects: Vec<Effect>,              // explicit effects list (NOT IN MINA)
    may_delegate: DelegationMode,      // analogous to may_use_token
}
```

### 2.4 Effects (NOT in Mina's model)

Pyana makes effects **explicit** on each action:
- SetField { cell, index, value }
- Transfer { from, to, amount }
- GrantCapability { from, to, cap }
- RevokeCapability { cell, slot }
- EmitEvent { cell, event }
- IncrementNonce { cell }
- CreateCell { public_key, token_id, balance }

In Mina, "effects" are implicit from the body fields: `balance_change`, `update.app_state`, `increment_nonce`, etc. The circuit constrains what can change.

### 2.5 Capability System (NOT in Mina)

Pyana's unique contribution: each cell has a **c-list** (capability list). A capability is:
```rust
CapabilityRef { target: CellId, slot: u32, permissions: AuthRequired, breadstuff: Option<[u8;32]> }
```

Rules:
- To act on another cell, the parent must hold a capability to it
- Capabilities can be granted (with attenuation only) and revoked
- `Breadstuff` authorization: a capability token hash as an alternative to sig/proof

### 2.6 DelegationMode (analogous to may_use_token)

- `None` - children cannot use parent's capabilities
- `ParentsOwn` - children can use parent's own capabilities
- `Inherit` - children inherit parent's delegation transitively

### 2.7 Execution (TurnExecutor)

The executor walks the call forest **depth-first** (pre-order):
1. Meter action base cost
2. Check target cell exists
3. Check capability: parent must hold access to target (or be self)
4. Check preconditions (cell state + network)
5. Verify authorization (sig/proof/breadstuff)
6. Apply effects (with per-effect permission checks)
7. Recurse into children (with delegation mode propagation)

Atomicity: journal-based rollback. If ANY action fails, the entire turn is rolled back.

---

## 3. What Pyana Is Missing

### 3.1 The Two-Pass Ledger (Critical)

Mina separates fee payer processing from the rest:
- **First pass**: fee payer always commits (fee is always taken)
- **Second pass**: all other updates are tentative; if any fail, the second pass ledger is not committed

Pyana's model is all-or-nothing: if the turn fails, the fee is refunded. This means:
- Validators cannot be compensated for processing invalid turns
- DoS potential: submit expensive-to-validate turns that always fail
- **Recommendation**: Add a two-phase execution model where the agent's fee + nonce are always committed regardless of turn success

### 3.2 Balance Change as Signed Amount + Excess Tracking

Mina tracks a **running excess** across all account updates:
- Each account update has a `balance_change: Amount.Signed`
- Withdrawals produce excess (available funds)
- Deposits consume excess
- At the end of the transaction, excess must be exactly zero (conservation)
- Only default-token balance changes count toward the excess

This is the mechanism for fund flow between accounts in a single transaction WITHOUT needing explicit "transfer" effects. Account A withdraws 100, Account B deposits 100, excess nets to zero.

Pyana uses explicit `Transfer { from, to, amount }` effects instead, which is more intuitive but:
- Loses the composability of balance_change (multiple unrelated circuits can independently declare their balance changes)
- Makes it harder for a proof circuit to abstractly "withdraw" without specifying the destination
- **Recommendation**: Consider adding a `balance_change: i64` field on Action (like Mina) alongside or instead of explicit Transfer effects. Use excess tracking to enforce conservation within a turn.

### 3.3 `proved_state` Tracking

Mina's `proved_state` flag is a powerful integrity mechanism:
- If all 8 state fields are set by a proof-authorized update, `proved_state = true`
- Subsequent preconditions can assert `proved_state = true`
- This guarantees the state was produced by the zkApp's own logic, not manually set by a deployer

Pyana has no equivalent. Any authorized party can set state fields arbitrarily.

**Recommendation**: Add a `proved_state: bool` field to CellState, with the same semantics.

### 3.4 Replay Protection (Subtler Than Nonce-Only)

Mina has THREE replay protection mechanisms:
1. Increment nonce + constant nonce precondition (standard)
2. `use_full_commitment` (depends on fee payer's nonce -- protects non-nonce-incrementing updates)
3. Non-signature updates don't need replay protection (proofs are stateless; replay just means re-execution)

Pyana only has mechanism (1) at the Turn level. Individual actions within a turn have no independent replay protection.

**Recommendation**: Consider per-action commitment binding (action signs over its position in the forest + the forest hash).

### 3.5 Account Preconditions on is_new

Mina can assert `is_new = true/false` in preconditions, allowing initialization logic:
- A zkApp can require `is_new = true` to gate deployment-time setup
- Combined with `proved_state`, this ensures first-run logic executed correctly

Pyana's preconditions don't include an `is_new` check.

### 3.6 `use_full_commitment` Semantics

In Mina, when `use_full_commitment = false`, the signature covers only the hash of the REMAINING account updates (excluding fee payer and memo). This allows composability: Alice can sign her part of a multi-party transaction without seeing Bob's part.

When `use_full_commitment = true`, the signature covers everything (fee payer + memo + all updates). This provides full transaction binding.

Pyana doesn't have this distinction -- the signing message is always the action hash (target + method + args + effects + delegation).

**Recommendation**: Add a `full_commitment: bool` flag so that some actions can be signed independently of the broader turn (enabling composable multi-party turns).

### 3.7 Action State (Rolling Hash History)

Mina maintains 5 action_state slots per account, acting as a rolling FIFO of action sequence hashes:
- New actions are pushed onto `s1`
- When the slot changes, `s1 -> s2 -> s3 -> s4 -> s5` shift
- This allows preconditions to reference recent action history

Pyana's `actions` concept doesn't exist in the cell model.

**Recommendation**: Add an action_state mechanism for zkApps that need to verify historical sequencing.

### 3.8 Timing / Vesting

Mina has a full vesting schedule system:
- `initial_minimum_balance`, `cliff_time`, `cliff_amount`, `vesting_period`, `vesting_increment`
- Checked on every balance-reducing operation

Pyana has no timing/vesting support.

### 3.9 Permission for Verification Key Has Transaction Version

Mina's `set_verification_key` permission is a tuple `(Auth_required, Txn_version)`. If the stored txn_version is older than current, the permission falls back to Signature (even if it was Proof/Impossible). This is a migration mechanism.

Pyana doesn't version its permissions.

### 3.10 Permissions Updated LAST

Mina explicitly applies permission changes as the **last** mutation in an account update. This ensures all other operations in the same update are gated by the OLD permissions.

Pyana's executor applies effects in declaration order, which means an action could theoretically set_permissions THEN use the new permissions for subsequent effects in the same action. This is a semantic bug risk.

---

## 4. What Pyana Does Better / Differently

### 4.1 Capability System (Object-Capability Model)

Mina's security model is purely **identity-based**: you authorize as yourself (signature/proof on YOUR account), and the permission system gates what you can do to YOUR OWN account. Cross-account interaction is limited to balance_change flowing through the excess.

Pyana adds **capability-based security**: cells hold explicit c-lists of capabilities to other cells. This enables:
- **Delegation**: grant a sub-capability to a child agent
- **Attenuation**: granted capabilities are always equal-or-narrower (never amplification)
- **Revocation**: capabilities can be revoked without changing the target cell

This is strictly more powerful than Mina's model for agent-to-agent interaction.

### 4.2 Breadstuff Authorization (Capability Tokens)

A fourth auth mode: present a capability token hash instead of a signature or proof. This enables:
- Bearer-token patterns
- Delegated authority without key sharing
- Programmatic authorization without ZK circuits

Mina has no equivalent.

### 4.3 Explicit Method Invocation

Pyana's actions have `method: Symbol` -- a hashed method name. This makes the call forest semantically meaningful: you're not just "updating account state" but "invoking a named method."

Mina's model is purely declarative: "here's what should change." The zkApp circuit enforces constraints, but there's no named-method concept on-chain.

This is better for:
- Indexing and querying (what methods were called?)
- Developer ergonomics
- Protocol evolution (different methods can have different costs)

### 4.4 Explicit Effects vs. Implicit State Diff

Pyana makes effects explicit: each action declares exactly what it will do. This is better for:
- Transparency: users can see exactly what will change before signing
- Metering: costs can be computed precisely from the effect list
- Validation: effects can be checked independently of execution

But worse for:
- Composability: in Mina, a proof circuit just says "balance_change = -X" without knowing where the funds go
- Circuit simplicity: Mina's model needs only to hash the body and verify it matches the circuit's output

### 4.5 Journal-Based Rollback

Pyana uses a journal (append-only log of old values) for rollback. This is more memory-efficient than Mina's approach of maintaining separate ledger copies.

However, Mina's two-pass model is semantically superior because fees are always collected.

### 4.6 Computron Metering

Pyana has explicit per-operation cost accounting (computrons). Mina uses a coarser cost model based on segment types (proof/signed_single/signed_pair) with a transaction-level cost limit.

Pyana's approach is better for:
- Fine-grained resource control
- Preventing compute-heavy attacks
- Fair pricing

### 4.7 Cross-Cell Effects

In Mina, you can only modify YOUR OWN account (the one matching the account update's public_key + token_id). Cross-account interaction is only through:
- Balance excess flow
- Token owner gating children
- Reading other accounts' state via preconditions

In Pyana, an action on cell A can produce effects on cell B (e.g., `SetField { cell: B, ... }`) IF A holds a capability to B. This enables richer inter-agent interaction patterns.

---

## 5. Specific Recommendations

### 5.1 Add Two-Phase Fee Commitment (High Priority)

```rust
// Phase 1: always commits
agent.balance -= fee;
agent.nonce += 1;
// Phase 2: tentative, rolled back on failure
// ... rest of execution
```

This prevents DoS and aligns validator incentives.

### 5.2 Add Balance Change + Excess Tracking (High Priority)

Each action should have an optional `balance_change: Option<i64>` that participates in a running excess. At turn end, excess must be zero. This enables:
- Proof circuits that withdraw without specifying destination
- Multi-party composed turns
- Conservation enforcement at the type level

Keep explicit `Transfer` effects as sugar/shorthand.

### 5.3 Add `proved_state` (Medium Priority)

```rust
pub struct CellState {
    pub fields: [FieldElement; 8],
    pub nonce: u64,
    pub balance: u64,
    pub proved_state: bool,  // NEW
}
```

Rules:
- If all 8 fields set + authorization is Proof -> proved_state = true
- If any field changed by non-Proof auth -> proved_state = false
- If fields unchanged -> proved_state unchanged

### 5.4 Permission Update Ordering (High Priority -- Bug Fix)

Effects should be applied in a specific order where permission changes are ALWAYS last. Or: check all permissions upfront against the ORIGINAL permissions, regardless of effect ordering.

### 5.5 Add Full/Partial Commitment (Medium Priority)

Add a `use_full_commitment: bool` to Action:
- `true`: signing message includes the entire turn hash
- `false`: signing message includes only this action's hash + position

Enables multi-party turn composition.

### 5.6 Consider Token Ownership via Capabilities (Keep Pyana's Approach)

Mina's token ownership model (derive token_id from owner account_id, require owner in call stack) maps naturally onto pyana's capability system:
- A token owner cell grants capabilities to token-holder cells
- The `DelegationMode` already provides the inheritance mechanism
- This is MORE GENERAL than Mina's model because:
  - Multiple cells can co-own a token domain
  - Capabilities can be attenuated (partial token rights)
  - Revocation doesn't require changing the token itself

**Keep the capability approach but add the constraint**: if `cell.token_id != DEFAULT_TOKEN`, the actor's capability chain must include authorization from a cell whose `CellId` derives that token_id.

### 5.7 Add Action State for Sequencing Proofs (Low Priority)

Only needed if/when zkApps need to verify ordering of past actions. Can be deferred.

### 5.8 Add `is_new` to Preconditions (Low Priority)

```rust
pub struct CellStatePrecondition {
    pub nonce: Option<u64>,
    pub min_balance: Option<u64>,
    pub field_equals: Vec<(usize, FieldElement)>,
    pub is_new: Option<bool>,          // NEW
    pub proved_state: Option<bool>,    // NEW (after 5.3)
}
```

---

## 6. Summary Table

| Feature | Mina | Pyana | Assessment |
|---------|------|-------|------------|
| Tree structure | Call forest (cons-hash) | Call forest (Merkle) | Equivalent |
| Traversal | Stack machine | DFS | Pyana simpler, both correct |
| Auth modes | Signature, Proof, None | Sig, Proof, Breadstuff, None | Pyana richer |
| Cross-cell | Via excess/token gating | Via capabilities | Pyana much richer |
| Balance flow | Signed balance_change + excess | Explicit Transfer effect | Mina more composable |
| Fee handling | Two-pass (fee always taken) | All-or-nothing | **Mina superior -- fix pyana** |
| State integrity | proved_state | Missing | **Add to pyana** |
| Permissions | 13 actions, checked per-update | 8 actions, checked per-effect | Mina more granular |
| Perm ordering | Permissions updated LAST | No ordering guarantee | **Fix in pyana** |
| Replay protection | 3 mechanisms | 1 (turn nonce) | **Strengthen pyana** |
| Method dispatch | Implicit (body fields) | Explicit (method symbol) | Pyana better UX |
| Effects | Implicit (body diff) | Explicit (effect list) | Trade-off |
| Metering | Coarse (segment type) | Fine (per-op computrons) | Pyana better |
| Composability | use_full_commitment | Single signing mode | **Add to pyana** |
| Token system | Derived token_id + owner gating | token_id + capabilities | Pyana more general |
| Delegation | may_use_token (3 modes) | DelegationMode (3 modes) | Equivalent semantics |
| Vesting/timing | Full schedule | None | Pyana missing (low priority) |
| Action history | 5-slot rolling action_state | None | Pyana missing (low priority) |
