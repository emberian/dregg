# DSL Redesign — `dregg` user-facing surface

**Status:** Proposed. Supersedes the ad-hoc surface audited in `AUDIT-dsl.md`.
**Companion:** Effect VM Shape A (`EFFECT-VM-SHAPE-A.md`).
**Scope of rewrite:** breaking. The codebase is 2 days old; we do not preserve
the current `ActionBuilder`, the standalone `CompoundTurn` / `SettlementAction`
types, the standalone `Settlement` payment type, or `Authorization::Unchecked`
as a default-constructible value.

---

## 0. North star

There is exactly one runtime executable, the `Turn` (`turn/src/turn.rs:71`). The
DSL is the entire path from *what the user wants* to that `Turn`. Today that
path has three competing exits (`Turn` / `CompoundTurn` / `Settlement`), a
silently-defaulting authorization, ten typed effect builders out of 41 variants,
and a `convert_effects_to_vm` (sdk/src/cipherclerk.rs:4322) that lies to the prover
by no-op'ing 22 variants.

The redesign collapses this into a single layered tower:

```
 +--------------------------------------------------------------+
 |  Intent       — "I want X" — declarative, ~12 variants       |  dregg_intent::dsl
 +--------------------------------------------------------------+
                       Lowering (deterministic, total, tested)
 +--------------------------------------------------------------+
 |  EffectPlan   — typed builders, all 41 variants reachable    |  dregg_turn::dsl
 +--------------------------------------------------------------+
                       Authorization + Sealing
 +--------------------------------------------------------------+
 |  SealedTurn   — Turn whose every Action carries proven auth  |  dregg_turn::SealedTurn
 +--------------------------------------------------------------+
                       Cipherclerk::submit (signs, attaches witnesses)
 +--------------------------------------------------------------+
 |  Turn         — runtime executable (unchanged shape)         |  dregg_turn::turn::Turn
 +--------------------------------------------------------------+
```

Everything else folds into this. `CompoundTurn`, `Settlement`,
`SettlementAction`, `RingTradeParticipant::settle_leg` all become *consumers* of
the same `Intent → EffectPlan → SealedTurn` pipeline. There is no third
unifying type; the unifier is the layer below them.

---

## 1. Three-way fragmentation: resolution

The audit's open question (`AUDIT-dsl.md` question 6) names three "what to
execute" types. The current state:

| Type | Source | Purpose | Consumer |
|------|--------|---------|----------|
| `Turn` | `turn/src/turn.rs:71` | runtime executable | `TurnExecutor` |
| `CompoundTurn` | `intent/src/trustless.rs:240` | output of `TrustlessIntentEngine::finalize` | **nothing** |
| `Settlement` + `SettlementAction` | `intent/src/solver.rs:62`, `trustless.rs:253` | a single transfer leg | `RingTradeParticipant::settle_leg` impls in apps |

`Turn` is canonical. The redesign:

**`CompoundTurn` becomes a thin newtype.** It is an `Intent` of kind
`Intent::RingSettlement { rings: Vec<Ring> }`. The trustless engine still
*produces* it (the engine's job is fair selection, not turn-building), but
finalize's return type changes:

```rust
pub fn finalize(&mut self) -> Result<RingSettlementIntent, EngineError>;

pub struct RingSettlementIntent {
    pub batch_id: u64,
    pub rings: Vec<RingTrade>,           // unchanged
    pub solver_id: [u8; 32],
    pub validity_proof_hash: [u8; 32],   // binding — required for replay-resist
}
```

The federation node calls `dregg_intent::lowering::lower(intent)` to get an
`EffectPlan`, then `cclerk.seal_and_submit(plan)`. The federation node is the
agent of record on the settlement; the solver_id is a witness on the action,
not a turn-level field.

**`Settlement` (intent/src/solver.rs:62-72) is unchanged in shape** — it is
still the canonical "this leg moves N of asset A from commitment X to
commitment Y" type. But it is reframed: it is the *output shape of one
edge of the ring graph*, not a thing that gets executed directly. The
Settlement → Effect lowering lives in `dregg_intent::lowering`.

**`RingTradeParticipant::settle_leg` is removed.** Apps no longer translate
`Settlement` into effects themselves. The lowering does it once,
deterministically, with test coverage. Apps that want to react to settlements
(e.g., AMM rebalancing) implement `SettlementObserver::on_settled(&Settlement,
&TurnReceipt)` — a *post-execution* hook, not a builder hook.

**Migration recipe:** Existing `RingTradeParticipant` impls in `app-framework`
(only the unit-test `DummyParticipant` in `ring_trade.rs:79` currently exists)
become `SettlementObserver`s. The `LegId` type stays as a correlation key.

---

## 2. ActionBuilder typestate

The audit found `ActionBuilder::new` defaults to `Authorization::Unchecked`
(`turn/src/builder.rs:169`) with no compile-time enforcement. The redesigned
builder makes "unauthorized" unrepresentable in the type system.

### Type-state markers

```rust
// turn/src/dsl/typestate.rs
pub trait AuthState: sealed::Sealed {}
pub trait EffectsState: sealed::Sealed {}

pub struct NeedsCaller;          // initial state
pub struct NeedsAuth;            // caller set, auth missing
pub struct Signed;               // ed25519 signature, ready
pub struct Proved;               // STARK proof bound to (action, resource)
pub struct Bearer;               // bearer-cap proof with delegation chain
pub struct Threshold { m: u8, n: u8 }; // m-of-n multisig
pub struct CapHeld;              // exercises a cap in the actor's c-list
pub struct UncheckedOptIn;       // only constructable via `unsafe fn`

pub struct NoEffects;            // build() rejects
pub struct HasEffects;           // build() accepts

impl AuthState for NeedsCaller {} impl AuthState for NeedsAuth {}
impl AuthState for Signed {}     impl AuthState for Proved {}
impl AuthState for Bearer {}     impl AuthState for Threshold {}
impl AuthState for CapHeld {}    impl AuthState for UncheckedOptIn {}
impl EffectsState for NoEffects {} impl EffectsState for HasEffects {}

mod sealed { pub trait Sealed {} /* impls for the markers above */ }
```

### Builder

```rust
pub struct ActionBuilder<A: AuthState = NeedsCaller, E: EffectsState = NoEffects> {
    target: CellId,
    method: Symbol,
    args: Vec<FieldElement>,
    auth: AuthSlot,             // private; only the typestate transitions write it
    preconditions: Preconditions,
    effects: Vec<Effect>,
    may_delegate: DelegationMode,
    commitment_mode: CommitmentMode,
    declared_excess: Option<i64>, // see §5
    children: Vec<ActionBuilder<Signed, HasEffects>>, // children must be fully built
    _phantom: PhantomData<(A, E)>,
}

// Entry: every constructor demands both a target AND a caller.
impl ActionBuilder<NeedsAuth, NoEffects> {
    pub fn new(target: CellId, method: &str, caller: CellId) -> Self { ... }
}

// Each authorization mode is its own typestate transition.
impl ActionBuilder<NeedsAuth, NoEffects> {
    pub fn authorize_signed(self, sig: Ed25519Signature)
        -> ActionBuilder<Signed, NoEffects>;

    pub fn authorize_proof(self, proof: ZkProofBytes,
                            bound: AuthBinding)
        -> ActionBuilder<Proved, NoEffects>;

    pub fn authorize_bearer(self, proof: BearerCapProof)
        -> ActionBuilder<Bearer, NoEffects>;

    pub fn authorize_threshold(self, sigs: ThresholdSignatures)
        -> ActionBuilder<Threshold, NoEffects>;

    pub fn authorize_via_capability(self, slot: CapabilitySlot)
        -> ActionBuilder<CapHeld, NoEffects>;

    /// Opt out of authorization. Requires `unsafe`. Only valid in cells whose
    /// permissions explicitly accept `AuthRequired::None`.
    pub unsafe fn authorize_unchecked(self)
        -> ActionBuilder<UncheckedOptIn, NoEffects>;
}

// Effects are only addable after authorization is set.
impl<A: AuthState, E: EffectsState> ActionBuilder<A, E>
where A: Authorized
{
    pub fn effect<F: TypedEffect>(self, f: F) -> ActionBuilder<A, HasEffects>;
    // typed helpers — see §3
}

// build() is only callable when both typestates are satisfied.
impl<A: Authorized> ActionBuilder<A, HasEffects> {
    pub fn build(self) -> Action;
}

trait Authorized: AuthState {} // sealed; not implemented for NeedsCaller/NeedsAuth
impl Authorized for Signed {}
impl Authorized for Proved {}
impl Authorized for Bearer {}
impl Authorized for Threshold {}
impl Authorized for CapHeld {}
impl Authorized for UncheckedOptIn {}
```

### Properties

- `ActionBuilder::new(...).build()` is a compile error: `NeedsAuth: !Authorized`
  and `NoEffects: !HasEffects`.
- The only way into the `Signed/Proved/...` states is via the corresponding
  `authorize_*` method that consumes a real witness.
- `unsafe fn authorize_unchecked` is grep-able and audit-flaggable; it does
  not appear in any reasonable production code path.
- `AuthSlot` is a private enum, the *only* place `Authorization::Unchecked` is
  constructable.

### Migration

`turn/src/builder.rs` becomes thin: the existing `TurnBuilder` stays (renamed
`Cipherclerk::turn(...)` to be reachable by the cclerk idiom, see §6), but takes
fully-built `Action`s rather than internal `ActionBuilder`s. This also fixes
finding 6 (the borrow-checker forbids sibling interleaving): callers build
each `ActionBuilder` to completion, then `turn.add(action)`.

---

## 3. Typed effect helpers — full coverage

Every one of the 41 runtime `Effect` variants
(`turn/src/action.rs:220-619`) gets a typed builder method. The audit found
only 10 (24%) have helpers. Below: every signature, grouped by family.

To keep call sites short, we introduce a small set of newtypes that the
helpers consume:

```rust
pub struct Amount(pub u64);
pub struct BalanceDelta(pub i64);
pub struct FieldIndex(pub u32);                // was usize — finding 20
pub struct CapabilitySlot(pub u32);
pub struct CapabilityHandle { target: CellId, slot: CapabilitySlot }
pub struct NoteValue { amount: Amount, asset: AssetId }
pub struct Commitment<T: Phantom> { bytes: [u8; 32], _t: PhantomData<T> }
pub struct NoteContent;  // phantoms; constrains Commitment<T> at type level
pub struct EscrowConditionExpr;
pub struct EscrowId([u8; 32]);
pub struct QueueHandle(CellId);
pub struct PortableSpendingProof(pub PortableNoteProof);
pub struct BridgeReceiptSig(pub BridgeReceipt);
pub struct FactoryVk([u8; 32]);
```

### §3.1 — Field & balance (3)

```rust
impl<A: Authorized> ActionBuilder<A, NoEffects | HasEffects> {
  // SetField (turn/src/action.rs:223)
  pub fn effect_set_field(self, cell: CellId, idx: FieldIndex, value: FieldElement)
    -> ActionBuilder<A, HasEffects>;

  // Transfer (turn/src/action.rs:229)
  pub fn effect_transfer(self, from: CellId, to: CellId, amount: Amount)
    -> ActionBuilder<A, HasEffects>;

  // IncrementNonce (turn/src/action.rs:245)
  pub fn effect_increment_nonce(self, cell: CellId)
    -> ActionBuilder<A, HasEffects>;
}
```

### §3.2 — Capabilities (5)

```rust
  // GrantCapability (action.rs:235)
  pub fn effect_grant(self, from: CellId, to: CellId, cap: CapabilityHandle)
    -> ActionBuilder<A, HasEffects>;

  // RevokeCapability (action.rs:241)
  pub fn effect_revoke(self, cell: CellId, slot: CapabilitySlot)
    -> ActionBuilder<A, HasEffects>;

  // Introduce (action.rs:403)
  pub fn effect_introduce(self,
        introducer: CellId, recipient: CellId, target: CellId,
        perms: AuthRequired)
    -> ActionBuilder<A, HasEffects>;

  // ExerciseViaCapability (action.rs:534)
  pub fn effect_exercise(self, slot: CapabilitySlot,
                          inner: impl IntoIterator<Item = Effect>)
    -> ActionBuilder<A, HasEffects>;

  // PipelinedSend (action.rs:409). Currently errors in apply_effect; we keep
  // the helper so apps can build it for trace, but the type signature explicitly
  // documents the unsupported status with a #[must_use] result that names the
  // EVM rejection — see EFFECT-VM-SHAPE-A.md "Group B" decision.
  #[must_use = "PipelinedSend is currently rejected by the executor; see Stage 3"]
  pub fn effect_pipeline(self, target: EventualRef, action: Action)
    -> ActionBuilder<A, HasEffects>;
```

### §3.3 — Notes & seal-pairs (5)

```rust
  // NoteSpend (action.rs:273)
  pub fn effect_note_spend(self,
        nullifier: Nullifier,
        merkle_root: NoteTreeRoot,
        value: NoteValue,
        proof: SpendingProof,
        committed_value: Option<ValueCommitmentBytes>)
    -> ActionBuilder<A, HasEffects>;

  // NoteCreate (action.rs:294)
  pub fn effect_note_create(self,
        commitment: Commitment<NoteContent>,
        value: NoteValue,
        encrypted: EncryptedNoteBytes,
        range_proof: Option<RangeProof>)
    -> ActionBuilder<A, HasEffects>;

  // CreateSealPair (action.rs:312)
  pub fn effect_create_seal_pair(self,
        sealer_holder: CellId, unsealer_holder: CellId)
    -> ActionBuilder<A, HasEffects>;

  // Seal (action.rs:319)
  pub fn effect_seal(self, pair: SealPairId, cap: CapabilityHandle)
    -> ActionBuilder<A, HasEffects>;

  // Unseal (action.rs:326)
  pub fn effect_unseal(self, box_: SealedBox, recipient: CellId)
    -> ActionBuilder<A, HasEffects>;
```

### §3.4 — Cell lifecycle (5)

```rust
  // CreateCell (action.rs:247)
  pub fn effect_create_cell(self,
        public_key: PublicKey, token_id: TokenId, initial_balance: Amount)
    -> ActionBuilder<A, HasEffects>;

  // CreateCellFromFactory (action.rs:554)
  pub fn effect_create_from_factory(self,
        factory: FactoryVk,
        owner: PublicKey, token_id: TokenId,
        params: FactoryCreationParams)
    -> ActionBuilder<A, HasEffects>;

  // MakeSovereign (action.rs:545)
  pub fn effect_make_sovereign(self, cell: CellId)
    -> ActionBuilder<A, HasEffects>;

  // SetPermissions (action.rs:259) — note: applied LAST in action
  pub fn effect_set_permissions(self, cell: CellId, perms: Permissions)
    -> ActionBuilder<A, HasEffects>;

  // SetVerificationKey (action.rs:266) — note: applied LAST in action
  pub fn effect_set_vk(self, cell: CellId, vk: Option<VerificationKey>)
    -> ActionBuilder<A, HasEffects>;
```

### §3.5 — Delegation (3)

```rust
  // SpawnWithDelegation (action.rs:334)
  pub fn effect_spawn_with_delegation(self,
        child_pk: PublicKey, child_token: TokenId, max_staleness_secs: u64)
    -> ActionBuilder<A, HasEffects>;

  // RefreshDelegation (action.rs:344)
  pub fn effect_refresh_delegation(self)
    -> ActionBuilder<A, HasEffects>;

  // RevokeDelegation (action.rs:347)
  pub fn effect_revoke_delegation(self, child: CellId)
    -> ActionBuilder<A, HasEffects>;
```

### §3.6 — Bridge (4)

```rust
  // BridgeMint (action.rs:358)
  pub fn effect_bridge_mint(self, portable: PortableSpendingProof)
    -> ActionBuilder<A, HasEffects>;

  // BridgeLock (action.rs:368)
  pub fn effect_bridge_lock(self,
        nullifier: Nullifier, destination: FederationId,
        value: NoteValue, timeout_height: BlockHeight,
        spending_proof: SpendingProof)
    -> ActionBuilder<A, HasEffects>;

  // BridgeFinalize (action.rs:386)
  pub fn effect_bridge_finalize(self,
        nullifier: Nullifier, receipt: BridgeReceiptSig)
    -> ActionBuilder<A, HasEffects>;

  // BridgeCancel (action.rs:397)
  pub fn effect_bridge_cancel(self, nullifier: Nullifier)
    -> ActionBuilder<A, HasEffects>;
```

### §3.7 — Obligations (3)

```rust
  // CreateObligation (action.rs:418)
  pub fn effect_create_obligation(self,
        beneficiary: CellId, condition: ProofCondition,
        deadline: BlockHeight, stake: Commitment<NoteContent>,
        stake_amount: Amount)
    -> ActionBuilder<A, HasEffects>;

  // FulfillObligation (action.rs:434)
  pub fn effect_fulfill_obligation(self, id: ObligationId, proof: ConditionProof)
    -> ActionBuilder<A, HasEffects>;

  // SlashObligation (action.rs:442)
  pub fn effect_slash_obligation(self, id: ObligationId)
    -> ActionBuilder<A, HasEffects>;
```

### §3.8 — Escrow (6)

```rust
  // CreateEscrow (action.rs:448)
  pub fn effect_create_escrow(self,
        from: CellId, recipient: CellId, amount: Amount,
        condition: EscrowConditionExpr,
        timeout: BlockHeight, id: EscrowId)
    -> ActionBuilder<A, HasEffects>;

  // ReleaseEscrow (action.rs:464)
  pub fn effect_release_escrow(self, id: EscrowId, proof: Option<ConditionProofBytes>)
    -> ActionBuilder<A, HasEffects>;

  // RefundEscrow (action.rs:472)
  pub fn effect_refund_escrow(self, id: EscrowId)
    -> ActionBuilder<A, HasEffects>;

  // CreateCommittedEscrow (action.rs:482)
  pub fn effect_create_committed_escrow(self, c: CommittedEscrowParams)
    -> ActionBuilder<A, HasEffects>;

  // ReleaseCommittedEscrow (action.rs:508)
  pub fn effect_release_committed_escrow(self,
        id: EscrowId, claim_auth: EscrowClaimAuth, recipient: CellId)
    -> ActionBuilder<A, HasEffects>;

  // RefundCommittedEscrow (action.rs:520)
  pub fn effect_refund_committed_escrow(self,
        id: EscrowId, claim_auth: EscrowClaimAuth, creator: CellId)
    -> ActionBuilder<A, HasEffects>;
```

### §3.9 — Events (1)

```rust
  // EmitEvent (action.rs:243)
  pub fn effect_emit(self, cell: CellId, topic: &str, data: Vec<FieldElement>)
    -> ActionBuilder<A, HasEffects>;
```

### §3.10 — Queues (6)

```rust
  // QueueAllocate (action.rs:569)
  pub fn effect_queue_allocate(self,
        capacity: u64, program_vk: Option<ProgramVk>)
    -> ActionBuilder<A, HasEffects>;

  // QueueEnqueue (action.rs:578)
  pub fn effect_queue_enqueue(self,
        queue: QueueHandle, message_hash: [u8; 32], deposit: Amount)
    -> ActionBuilder<A, HasEffects>;

  // QueueDequeue (action.rs:589)
  pub fn effect_queue_dequeue(self, queue: QueueHandle)
    -> ActionBuilder<A, HasEffects>;

  // QueueResize (action.rs:596)
  pub fn effect_queue_resize(self, queue: QueueHandle, new_capacity: u64)
    -> ActionBuilder<A, HasEffects>;

  // QueueAtomicTx (action.rs:605)
  pub fn effect_queue_atomic(self, ops: Vec<QueueTxOp>)
    -> ActionBuilder<A, HasEffects>;

  // QueuePipelineStep (action.rs:611)
  pub fn effect_queue_pipeline(self,
        pipeline: PipelineId, source: QueueHandle, sinks: Vec<QueueHandle>)
    -> ActionBuilder<A, HasEffects>;
```

### §3.11 — Nameservice (NEW VARIANT)

The audit (finding "open question #9") noted `sdk/src/names.rs:659` comments
`// 2. Submit Effect::RegisterName to the federation` but no such variant
exists. The new variant goes into `turn/src/action.rs`:

```rust
RegisterName {
    /// The name being registered, canonicalized.
    name: NameRecord,
    /// The cell that owns the name post-registration.
    owner: CellId,
    /// The TTL in blocks; renewal must happen before this expires.
    ttl_blocks: u64,
    /// Optional bond, slashed on TLD-policy violation.
    bond: Option<Amount>,
},
```

DSL helper:

```rust
  pub fn effect_register_name(self,
        name: NameRecord, owner: CellId, ttl: u64, bond: Option<Amount>)
    -> ActionBuilder<A, HasEffects>;
```

This makes the count of `Effect` variants **42**, and the DSL covers every
one of them.

### Coverage check

The DSL is generated/verified by a const-fn test:

```rust
#[test]
fn dsl_covers_every_effect_variant() {
    // turn/src/dsl/coverage.rs
    // Uses an `EffectKind` enum that is `#[derive(EnumIter)]` plus a build.rs
    // assertion that every kind has a corresponding `effect_*` method.
    let kinds: HashSet<_> = EffectKind::iter().collect();
    let covered = dregg_turn::dsl::ALL_HELPER_KINDS;
    assert_eq!(kinds, covered.iter().copied().collect());
}
```

---

## 4. Intent → Effect lowering

### Intent enum (small, high-level)

The current `intent/` crate conflates *capability matching* (`MatchSpec`,
`IntentKind`) with *exchange intent* (`ExchangeSpec` in `exchange.rs`,
`solver::IntentNode`) with *trustless settlement* (`CompoundTurn`). The
redesign separates:

- **`MatchSpec` / `IntentKind` (Need/Offer/Query)** — *discovery* intents.
  These do not lower to effects; their job is to find a `Match`. They stay in
  `dregg_intent::matcher`.
- **`dregg_intent::dsl::Intent`** — *executable* intents. These lower to
  `EffectPlan` via `Lowering`. This is the new canonical user-facing surface.

```rust
// dregg_intent/src/dsl.rs

/// An executable user intention. ~12 variants, each maps to one of a few
/// well-understood effect patterns.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Intent {
    /// Simple value transfer.
    Pay { from: CellId, to: CellId, amount: Amount, asset: AssetId },

    /// Pay only when a condition is satisfied; refundable on timeout.
    EscrowedPay {
        from: CellId, to: CellId, amount: Amount,
        condition: EscrowConditionExpr, timeout: BlockHeight,
    },

    /// Confidential note transfer (Pedersen-committed amount).
    NotePay {
        spend: Vec<NoteSpec>,       // notes to consume
        create: Vec<NoteSpec>,      // notes to produce
        conservation_proof: ConservationProof,
    },

    /// Atomic multi-party ring settlement (output of TrustlessIntentEngine).
    RingSettlement {
        rings: Vec<RingTrade>,
        solver_id: SolverId,
        validity_proof_hash: [u8; 32],
    },

    /// Two-way intent fulfillment: payer commits to pay-on-proof.
    Fulfill {
        intent_id: IntentId, payer: CellId, fulfiller: CellId,
        amount: Amount, predicate_proofs: Vec<PredicateProof>,
    },

    /// Capability grant/delegation.
    Delegate {
        from: CellId, to: CellId, cap: CapabilityHandle,
        bearer_expires_at: Option<BlockHeight>,
    },

    /// Cell creation (managed or sovereign).
    SpawnCell { spec: CellSpec },

    /// Bridge a note in or out.
    Bridge(BridgeAction),

    /// Programmable queue op.
    Queue(QueueAction),

    /// Name registration / renewal.
    Name(NameAction),

    /// Custom: drop into raw effects with explicit opt-in.
    /// Used when the high-level surface is insufficient (e.g. cell-specific
    /// programs). Forces the user to write an `EffectPlan` directly.
    Custom(CustomIntent),
}
```

### The `Lowering` trait

```rust
// dregg_intent/src/lowering.rs

pub trait Lowering {
    /// Lower this intent into a sequence of effects targeted at specific cells.
    ///
    /// MUST be deterministic and total: same input → same output, every variant
    /// has a non-empty (or explicitly-empty) result.
    fn lower(self, ctx: &LoweringContext) -> EffectPlan;
}

impl Lowering for Intent { /* one match arm per variant */ }

pub struct LoweringContext {
    pub current_height: BlockHeight,
    pub network_params: NetworkParams,
    // Resolves abstract CellIds (e.g. "my cclerk") to concrete ones.
    pub address_book: AddressBook,
}

pub struct EffectPlan {
    pub actions: Vec<PendingAction>,
}

pub struct PendingAction {
    pub target: CellId,
    pub method: Symbol,
    pub effects: Vec<Effect>,
    pub balance_change_derivation: BalanceDerivation, // see §5
    pub auth_hint: AuthHint,                          // see §6
}
```

### Properties (with tests)

```rust
// dregg_intent/src/lowering/tests.rs

#[test] fn lowering_is_total() {
    // For every variant of Intent (via EnumIter), construct a default
    // value and prove `lower()` does not panic / returns Ok.
}

#[test] fn lowering_is_deterministic() {
    let i = Intent::Pay { ... };
    assert_eq!(i.clone().lower(&ctx), i.lower(&ctx));
}

#[test] fn lowering_is_order_preserving_for_atomic_intents() {
    // RingSettlement with rings = [A, B, C] lowers to actions whose forest
    // root order matches [A, B, C]. This is binding: a federation that
    // reorders the lowered effects would produce a different turn hash.
}

#[test] fn lowering_is_injective_modulo_address_book() {
    // Two semantically-distinct intents → two distinct EffectPlan ids,
    // unless they differ only in unresolved AddressBook entries.
}
```

### Where the lowering lives

- `intent/src/lowering.rs` — `impl Lowering for Intent`
- `intent/src/lowering/ring.rs` — `RingSettlement` → `Vec<PendingAction>` (the
  per-edge `Settlement` → `Effect::Transfer` mapping; or
  `Effect::NoteSpend/NoteCreate` when the settlement is over committed notes)
- `intent/src/lowering/fulfillment.rs` — replaces the inline turn-builder at
  `intent/src/fulfillment.rs:783-832` (which the audit found is broken with
  unset nonce + Unchecked auth, finding 12). The body is moved here; the
  nonce becomes a *lowering parameter* obtained from
  `LoweringContext.address_book`, and the auth is left as an `AuthHint::Signed`
  to be filled in at `seal()` time.
- `intent/src/lowering/escrow.rs` — replaces `app-framework/src/escrow.rs`
  hand-built turns (finding 1).

### RingSolver fold-in

The audit's question 6 asks how `RingSolver` and `TrustlessIntentEngine` fit.
Answer:

- `RingSolver::find_rings` (`intent/src/solver.rs:117`) still produces
  `Vec<RingTrade>`. Unchanged.
- `TrustlessIntentEngine::finalize` produces a `RingSettlementIntent`, which
  is the `Intent::RingSettlement` variant. The standalone `CompoundTurn` and
  `SettlementAction` types are **removed**. Their replacement is the
  `Lowering` of `Intent::RingSettlement`.
- `RingTradeParticipant::settle_leg` (`app-framework/src/ring_trade.rs:64`)
  is **removed**. The lowering does the translation once; apps observe via
  `SettlementObserver::on_settled`.

---

## 5. Conservation enforcement

The audit's finding 4 showed `apps/gallery/src/settlement.rs:92,110` declares
`balance_change` deltas that don't match the actual `Transfer` amounts (one
is +winning_bid, the other is +1 for the NFT). The DSL pretends to enforce
conservation but actually doesn't.

### Redesign

- **`Action::balance_change` is removed from the public field surface.**
  `Action` still has it (the runtime needs the per-action delta for Mina-style
  excess tracking), but it is `pub(crate)` in `turn/src/action.rs` and only
  the `ActionBuilder::build()` can set it.
- **The framework derives `balance_change` from emitted `Transfer` /
  `NoteSpend` / `NoteCreate` / `CreateEscrow` / `ReleaseEscrow` /
  `RefundEscrow` effects.** Specifically:

```rust
// turn/src/dsl/conservation.rs
fn derive_balance_change(target: CellId, effects: &[Effect]) -> i64 {
    let mut delta: i64 = 0;
    for e in effects {
        delta = delta.checked_add(match e {                       // checked, not saturating (finding 15)
            Effect::Transfer { from, to, amount } if *from == target => -(*amount as i64),
            Effect::Transfer { from, to, amount } if *to == target   =>  (*amount as i64),
            Effect::NoteSpend { value, .. }                          => -(*value as i64),
            Effect::NoteCreate { value, .. }                         =>  (*value as i64),
            Effect::CreateEscrow { cell, amount, .. } if *cell == target => -(*amount as i64),
            Effect::ReleaseEscrow { .. }   => 0, // released to recipient — recipient's action
            Effect::RefundEscrow  { .. }   => 0, // executor decides
            _                              => 0,
        })?;
    }
    Ok(delta)
}
```

- **Excess declaration is explicit.** Sovereign cells *may* have legitimate
  unconserved deltas (e.g., an AMM whose state field maps to "off-chain
  reserves"). They opt in by calling `with_declared_excess(BalanceDelta)`:

```rust
impl<A: Authorized> ActionBuilder<A, HasEffects> {
    /// Declare a non-zero unconserved balance delta. Required when the action's
    /// emitted effects do not sum to `balance_change`. Only meaningful for
    /// sovereign cells (the executor enforces this).
    pub fn with_declared_excess(self, excess: BalanceDelta)
        -> ActionBuilder<A, HasEffects>;
}
```

- **The `validate_excess` check (`turn/src/builder.rs:129`) becomes total and
  uses `checked_add`** (closing finding 15).
- **The turn-level invariant** is: `sum(derived_balance_change_of_each_action)
  + sum(declared_excess) == 0`. The validator at submit time rejects with
  `ConservationViolation { derived, declared }`.

The gallery bug becomes a *compile-time impossibility*: the user never writes
`balance_change`; the framework writes it. The two `Transfer { amount: 1 }`
and `Transfer { amount: winning_bid }` actions are correctly derived (the NFT
transfer is balance 0 if `1 == 1`, the payment is balance `±winning_bid`).
The conservation check now correctly fails the buggy gallery code, telling
the developer their effects don't pair.

---

## 6. Authorization plumbing

The DSL exposes the four authorization modes as first-class typestate
transitions (see §2). Here is how each mode threads through the layers.

### 6.1 Per-action signature (most common)

```rust
let action = ActionBuilder::new(target, "transfer", caller)
    .effect_transfer(caller, recipient, Amount(100))
    .build_unsigned()                    // -> UnsignedAction
    .sign_with(&caller_keypair);         // -> Action<Signed>
```

`build_unsigned()` is available on `ActionBuilder<NeedsAuth, HasEffects>` —
it produces an `UnsignedAction` whose `sign_with` consumes a `Keypair` and
emits an `Action` in the `Signed` state.

### 6.2 Composite turn signature (one sig over whole turn)

```rust
let turn = TurnBuilder::new(agent, nonce)
    .add_unsigned_action(action_a)
    .add_unsigned_action(action_b)
    .sign_compound(&agent_keypair);   // -> SealedTurn
```

Each action's `commitment_mode` is set to `CommitmentMode::Full` automatically.
The signature covers the turn hash. This is the path the cclerk uses for its
own turns.

### 6.3 Capability-based (the c-list lookup)

```rust
let action = ActionBuilder::new(target, "transfer", caller)
    .authorize_via_capability(CapabilitySlot(7))   // -> Authorized<CapHeld>
    .effect_transfer(caller, recipient, Amount(100))
    .build();
```

At `seal()` time, the framework checks the caller's c-list, materializes the
capability, and emits an `Effect::ExerciseViaCapability` wrapper (rather than
a direct effect call). This wires §3.2's `effect_exercise` into the
authorization layer rather than requiring the user to write it explicitly.

### 6.4 Threshold (M-of-N)

```rust
let unsigned = ActionBuilder::new(target, "release", caller)
    .effect_release_escrow(escrow_id, Some(proof))
    .build_unsigned();

let partial1 = unsigned.partial_sign(&keypair_a);     // -> PartialSignedAction
let partial2 = partial1.partial_sign(&keypair_b);     // accumulates
let signed   = partial2.try_seal(threshold_policy)?;  // -> Action<Threshold>
```

Underneath, `Action.authorization` becomes a new variant `Threshold {
sigs: Vec<(PublicKey, Ed25519Sig)>, policy: ThresholdPolicy }`, added to
`Authorization` in `turn/src/action.rs`. The executor verifies that ≥M of N
public keys are in the cell's permitted-signer set.

### 6.5 Bearer caps

`authorize_bearer(BearerCapProof)` already exists in spirit
(`Authorization::Bearer` at `turn/src/action.rs:111`). The DSL surface gets
a builder: `BearerCapProof::build(delegator, bearer, cap, expires_at,
revocation_channel, allowed_effects)`.

### `AuthHint` (intent-to-action transition)

The lowering layer doesn't know which key signs an action — that's a cclerk
concern. So `PendingAction.auth_hint` is one of:

```rust
pub enum AuthHint {
    Signed,                                // use the agent's primary key
    Proved { binding: AuthBinding },       // STARK auth, with binding spec
    Threshold { policy: ThresholdPolicy }, // gather M-of-N
    Bearer { template: BearerTemplate },   // bearer cap, parameters known
    ViaCapability { slot: CapabilitySlot }, // look up in c-list
}
```

`Cipherclerk::seal(plan: EffectPlan) -> SealedTurn` walks each `PendingAction`,
follows the hint, produces a fully-authorized `Action`, and assembles the
`SealedTurn` (which is just a `Turn` plus an attestation that every action
is in an `Authorized` state).

---

## 7. App-framework consistency

The audit found `EscrowManager` (`app-framework/src/escrow.rs:64`) ships every
turn with `Authorization::Unchecked` (P0, finding 1). The redesign makes auth
a *required constructor parameter* on every framework helper, and removes the
ability to instantiate any framework helper that constructs an `Unchecked`
action without going through the `unsafe fn authorize_unchecked` typestate
escape hatch.

### New shape: `Authorizer`

```rust
// app-framework/src/auth.rs (already exists; expanded)

pub trait Authorizer {
    /// Sign or otherwise authorize an unsigned action.
    fn authorize(&self, unsigned: UnsignedAction) -> Result<Action, AuthError>;
}

pub struct WalletAuthorizer<'a> { cclerk: &'a AgentCipherclerk, identity: KeyHandle }
pub struct ProofAuthorizer    { binding: AuthBinding, prover: Box<dyn Prover> }
pub struct ThresholdAuthorizer{ partials: Vec<KeyHandle>, policy: ThresholdPolicy }
pub struct CapabilityAuthorizer { slot: CapabilitySlot }

/// Loud, audit-flaggable opt-out. Constructable only when the caller has
/// already verified that the target cell's permissions allow Unchecked.
pub struct UncheckedAuthorizer { _proof_of_acknowledgement: AckUnsafeUncheckedAuth }
```

### Manager constructors

```rust
impl<'a> EscrowManager<'a> {
    pub fn new(engine: &'a mut DreggEngine, auth: Box<dyn Authorizer>) -> Self;
}

impl<'a> RingTradeCoordinator<'a> {        // (was ring_trade.rs)
    pub fn new(engine: &'a mut DreggEngine, auth: Box<dyn Authorizer>) -> Self;
}

impl<'a> QueueEndpoint<'a> {
    pub fn new(engine: &'a mut DreggEngine, auth: Box<dyn Authorizer>) -> Self;
}

impl<'a> InboxEndpoint<'a> {
    pub fn new(engine: &'a mut DreggEngine, auth: Box<dyn Authorizer>) -> Self;
}

impl<'a> BlindedEndpoint<'a> {
    pub fn new(engine: &'a mut DreggEngine, auth: Box<dyn Authorizer>) -> Self;
}
```

The `Authorization::Unchecked` variant **does not appear** in any
`app-framework/src/*.rs` source file. A CI check (`grep -rn
'Authorization::Unchecked' app-framework/src/ && exit 1`) enforces this.

### Sentinel-CellId removal

Finding 11: `EscrowManager::release_with_proof` uses
`CellId::from_bytes(escrow_id)` as the agent. The redesign passes the caller's
CellId explicitly and uses it as the turn agent. The `Authorizer` then signs
under the caller's key. Escrow release no longer invents an identity.

### Escrow ID collision

Finding 14: `compute_escrow_id` collides on duplicate (from, to, amount,
timeout) tuples. The redesign adds a salt sourced from the *caller-supplied*
fields (a nonce in the caller's cclerk state, plus the current block height):

```rust
fn compute_escrow_id(from: &CellId, to: &CellId, amount: u64,
                      timeout: u64, salt: u64, height: u64) -> [u8; 32]
```

---

## 8. Coverage matrix and migration

Below: each existing app's effect-emission pattern, and what changes for it
under the new DSL.

### Apps that work as-is (no rewrite needed)

| App | Status | Notes |
|-----|--------|-------|
| `apps/identity` | clean | no `Effect::*` literal calls; uses higher-level cclerk API |
| `discord-bot` (toplevel) | clean | bot framework only; no DSL surface |
| `apps/privacy-voting` | clean | uses sealed-pair API; will get `effect_create_seal_pair` etc. as a bonus |

### Apps that need straightforward DSL migration

| App | Current pattern | Migration |
|-----|----------------|-----------|
| `apps/compute-exchange` | `Effect::CreateEscrow` / `ReleaseEscrow` literals (`settlement.rs:177-229`) | replace with `Intent::EscrowedPay` and `effect_release_escrow` |
| `apps/orderbook` | `Effect::CreateEscrow` / `Release` / `Refund` literals (`escrow.rs:129-154`, `settlement.rs:70-169`) | same; plus `Intent::RingSettlement` for multi-fill orders |
| `apps/gallery` | `Effect::Transfer` + `Effect::ReleaseEscrow` literals with broken `balance_change` (`settlement.rs:73-111`, finding 4) | `Intent::EscrowedPay` for bid lock; `Intent::Pay` for transfer; conservation now derived (fixes finding 4) |
| `apps/lending` | hand-built turns | `Intent::EscrowedPay` for collateral; `Intent::Pay` for repayment |
| `apps/stablecoin` | hand-built turns | `Intent::Pay` (cash leg); custom intent for mint/burn |
| `apps/amm` | `RingTradeParticipant` impl | becomes `SettlementObserver` (§1) |
| `apps/dao-treasury` | hand-built turns | `Intent::Pay` + threshold auth (§6.4) |
| `apps/subscription` | hand-built turns | `Intent::EscrowedPay` with periodic release |
| `apps/prediction-market` | hand-built turns | `Intent::EscrowedPay` for stake; `Intent::Pay` for payout |
| `apps/bounty-board` | hand-built turns | `Intent::Fulfill` |
| `apps/governed-namespace` | uses nameservice | gets `Intent::Name` (uses new `Effect::RegisterName`, §3.11) |

### Apps with unreachable effects (silently broken)

The audit found 22 unreachable variants. None of the apps actually emit:
- `CreateCommittedEscrow`, `ReleaseCommittedEscrow`, `RefundCommittedEscrow`
- `BridgeMint`, `BridgeLock`, `BridgeFinalize`, `BridgeCancel`
- `SpawnWithDelegation`, `RefreshDelegation`, `RevokeDelegation`
- `CreateSealPair`, `Seal`, `Unseal`
- `ExerciseViaCapability`
- `MakeSovereign`, `CreateCellFromFactory`
- `QueueAllocate`, `QueueResize`, `QueueAtomicTx`, `QueuePipelineStep`
- `PipelinedSend`

These are *runtime-only* features whose only consumers today are tests inside
`turn/` and `circuit/`. They have not gone unused because the apps decided
against them — they have gone unused because no app could reach them.

**Migration:** the new DSL surfaces them all (§3). Two apps that *should*
have been using them but are silently emitting nothing:

- `apps/nameservice/src/main.rs:217` (`register_name` handler) — should emit
  `Effect::RegisterName` (the new variant from §3.11). Currently the handler
  reaches into the storage layer directly with no turn at all. **Migration:
  rewrite the handler to call `Intent::Name(NameAction::Register {..})`.**
- `apps/privacy-voting` — should be using `Effect::CreateSealPair` /
  `Effect::Seal` / `Effect::Unseal` for sealed ballots, but currently uses
  ad-hoc field commitments. **Migration: rewrite the ballot
  encryption/decryption to use the seal-pair effects.**

### App-framework helpers

| Helper | Current state | Migration |
|--------|---------------|-----------|
| `escrow::EscrowManager` | `Unchecked` everywhere (finding 1) | requires `Authorizer` in `new()` (§7) |
| `ring_trade::RingTradeParticipant` | trait with `settle_leg` | replaced by `SettlementObserver` (§1) |
| `queue_endpoint::QueueEndpoint` | doesn't actually use `Effect::Queue*` (audit coverage matrix) | rewritten to emit `Intent::Queue` |
| `inbox_endpoint`, `blinded_endpoint` | no auth plumbing | take `Authorizer` (§7) |
| `batch_executor::ClientTurnRequest` | opaque `turn_bytes: Vec<u8>` (finding 10) | becomes `turn: SealedTurn, schema_version: u32` |

---

## 9. Bugs fixed on migration

The redesign closes the following audit-identified bugs *as a direct
consequence of the new design* (i.e. cannot be re-introduced without re-doing
the design):

| Audit # | Bug | Fixed by |
|---------|-----|----------|
| 1 | `EscrowManager` ships `Unchecked` | §7 `Authorizer` constructor parameter |
| 3 | `ActionBuilder::new` defaults to `Unchecked` | §2 typestate; `Unchecked` reachable only via `unsafe` |
| 4 | `gallery` lies about `balance_change` | §5 framework derives, not user-written |
| 5 | `solver.rs:328-332` `.min(x).max(x)` collapse | §5 lowering test for ring settlement amounts; the lowering uses the correct `min` (mirrors `find_rings` at solver.rs:202-211) and the buggy code is deleted along with `validate_ring`'s independent settlement-builder |
| 6 | builder borrow forbids sibling actions | §2 `ActionBuilder` is owned, attached via `turn.add(action)` |
| 7 | `build_authorized_turn` hardcodes `nonce: 0` (sdk/src/cipherclerk.rs:2441) | §4 lowering takes nonce from `LoweringContext.address_book` (which knows the cipherclerk's current nonce); `Cipherclerk::seal()` increments before submission |
| 8 | epoch bit-overlap (intent/src/lib.rs:535-536) | new `compute_stake_nullifier` uses 3 field elements covering bits [0,22), [22,44), [44,64); BLAKE3 backstop unchanged |
| 9 | only 10/41 variants in DSL | §3 covers all 42 (now incl. `RegisterName`) |
| 12 | `create_fulfillment_turn` nonce/auth (finding 12) | §4 fulfillment lowering takes nonce; auth via `AuthHint::Signed` |
| 13 | `convert_effects_to_vm` drops `cap.target` | §3 capability handle includes both fields; full-width Poseidon2 (Shape A Stage 1) |
| 14 | escrow id collisions | §7 salted by caller-supplied nonce + height |
| 15 | `compute_excess` saturating arithmetic | §5 `checked_add`, returns `ConservationOverflow` |
| 17 | trustless engine settled_batches grows unbounded | unrelated to DSL; flagged for separate fix |
| 18 | compatibility score inverts ordering | replaced with binary `feasible/not-feasible` |
| 19 | `MockProofVerifier` default | `TrustlessIntentEngine::new` is `cfg(test)` only; production uses `with_verifier` |
| 20 | `usize` for field index | §3 `FieldIndex(u32)` newtype |

### Bugs the redesign explicitly does NOT fix (out of DSL scope)

- Finding 2 (`convert_effects_to_vm` 4-byte truncation): handled by Effect VM
  Shape A Stage 1.
- Finding 16 (wire alias for `None` → `Unchecked`): the old wire alias is
  removed by the typestate work since no codepath ever emits `Unchecked` by
  default. Keep the `#[serde(alias = "None")]` for one release cycle to
  accept old payloads, then drop.

---

## 10. Surface for the unstaged `trustless.rs` / `solver.rs`

Audit's question 10: integrate or remove?

**Decision: integrate, with the modifications below.**

### `intent/src/solver.rs`

- Keep `IntentNode`, `RingTrade`, `Settlement`, `RingSolver` as-is.
- Fix finding 5 by deleting the duplicate settlement-builder in `validate_ring`
  (`solver.rs:323-339`) and reusing `find_rings`'s correct one
  (`solver.rs:202-211`). The same code path always produces the settlement.
- Fix finding 18 by replacing the `is_compatible` score with a feasibility
  bool. Ring scoring is *participant count* (already used in `validate_ring`
  at line 344), not edge-rate goodness.

### `intent/src/trustless.rs`

- Keep all 7 layers as-is.
- Replace `CompoundTurn` (line 240) and `SettlementAction` (line 253) with
  `Intent::RingSettlement` (§4). Both types are removed.
- `finalize()` returns `RingSettlementIntent`; the federation calls
  `intent.lower(&ctx)` to obtain an `EffectPlan` and submits it via the
  standard `Cipherclerk::seal_and_submit` path.
- `MockProofVerifier` becomes `#[cfg(test)] pub` and is removed from the
  `TrustlessIntentEngine::new` default. The non-test constructor requires
  `with_verifier(verifier: Box<dyn ProofVerifier>)`.
- `settled_batches` grows unbounded (finding 17): add `prune_before(batch_id)`
  and require call after every `finalize()` past the retention horizon.

### Integration test

A new end-to-end test in `intent/tests/trustless_to_turn.rs`:

```rust
#[test]
fn trustless_settlement_produces_valid_turn() {
    // 1. submit encrypted intents
    // 2. simulate threshold decryption
    // 3. submit a solver solution with a real (mock) proof
    // 4. close challenge window
    // 5. finalize -> RingSettlementIntent
    // 6. lower -> EffectPlan
    // 7. seal -> SealedTurn
    // 8. submit to a real TurnExecutor
    // 9. assert the receipt records all expected transfers
}
```

This test is the proof that the integration is complete; without it, the
trustless engine's output remains theoretical.

---

## 11. Migration plan and rollout

### Phase A — Foundations (week 1)

- [ ] `turn/src/dsl/typestate.rs` — new module with the AuthState/EffectsState markers.
- [ ] `turn/src/dsl/conservation.rs` — `derive_balance_change` (§5).
- [ ] `turn/src/action.rs` — `balance_change` becomes `pub(crate)`; add new `Threshold` and `RegisterName` variants.
- [ ] Remove `Authorization::Unchecked` default from `ActionBuilder::new`; delete the old `ActionBuilder` and `TurnBuilder`.
- [ ] New `dregg_turn::dsl::{ActionBuilder, TurnBuilder}` in `turn/src/dsl/mod.rs`.

### Phase B — Effect coverage (week 1-2)

- [ ] All 42 `effect_*` methods on `ActionBuilder<Authorized, _>` (§3).
- [ ] `dsl_covers_every_effect_variant` test passes.

### Phase C — Intent layer (week 2)

- [ ] `intent/src/dsl.rs` — the `Intent` enum (§4).
- [ ] `intent/src/lowering/*` — `Lowering` trait + per-variant impls.
- [ ] Totality / determinism / order-preservation / injectivity tests.
- [ ] Fold `intent/src/fulfillment.rs` turn-builders into `lowering/fulfillment.rs`.

### Phase D — Trustless / solver fold-in (week 2-3)

- [ ] Delete `CompoundTurn`, `SettlementAction`.
- [ ] `TrustlessIntentEngine::finalize` returns `RingSettlementIntent`.
- [ ] Fix solver settlement-amount collapse; remove duplicate builder.
- [ ] Add `intent/tests/trustless_to_turn.rs`.

### Phase E — App-framework rewrite (week 3)

- [ ] `EscrowManager`, queue/inbox/blinded endpoints take `Authorizer`.
- [ ] Delete `RingTradeParticipant`; introduce `SettlementObserver`.
- [ ] CI grep-guard: no `Authorization::Unchecked` in `app-framework/src/`.

### Phase F — App migration (week 3-4)

- [ ] Each app rewritten per §8 table.
- [ ] `apps/nameservice` emits `Effect::RegisterName` (was emitting nothing).
- [ ] `apps/gallery` switches to `Intent::EscrowedPay` (closes finding 4).
- [ ] `apps/privacy-voting` uses seal-pair effects (was hand-rolling).

### Phase G — Cipherclerk alignment (week 4)

- [ ] `Cipherclerk::seal(plan: EffectPlan) -> SealedTurn`.
- [ ] `Cipherclerk::submit(sealed: SealedTurn) -> TurnReceipt`.
- [ ] Delete `build_authorized_turn` (replaced by `seal_and_submit(plan)`).
- [ ] `convert_effects_to_vm` is total per Shape A Stage 1.

---

## 12. Invariants the DSL maintains

The redesigned DSL provides, at compile time and at test time, the following
guarantees:

1. **No unauthorized actions reach the executor.** Compile-time: an `Action`
   in the `NeedsAuth` typestate has no `build()` method. `Authorization::Unchecked`
   is only constructable via `unsafe`.
2. **Conservation is honest.** `balance_change` is derived, not declared. A
   declared excess is opt-in and labeled.
3. **Every runtime effect is reachable through a typed helper.** Tested by
   `dsl_covers_every_effect_variant`.
4. **Every intent has a deterministic, total lowering to effects.** Tested by
   the lowering totality + determinism tests.
5. **One canonical executable type.** `Turn` is the only thing the executor
   accepts; the rest of the surface is layered on top.
6. **No nonce-0 footguns.** Nonces are taken from the lowering context, not
   hardcoded. The cipherclerk's nonce-management lives in one place.
7. **CI grep-guards** prevent regression of (a) `Authorization::Unchecked` in
   `app-framework/src/`, (b) `nonce: 0` in any constructor, (c) hand-rolled
   `Action { ... }` literals outside `turn/src/dsl/` and tests.

---

## 13. Out of scope / future work

- **Per-action gas / computron limits as DSL surface.** Currently the turn
  fee is a single `u64`. A future redesign may distribute it across actions.
- **PIR-based intent matching as a DSL surface.** Currently in
  `intent/src/pir.rs`, exposed via lower-level APIs only.
- **`dregg-dsl` (the source-to-circuit DSL).** The audit's question 3 asks
  whether this should converge with the framework DSL. Answer: not yet.
  `dregg-dsl` produces *circuits*; this DSL produces *turns*. They are
  consumed by orthogonal subsystems (the prover vs. the executor). A
  future round may add a "deploy this circuit as a custom program" intent
  that bridges the two.

---

## 14. Summary

The current DSL is a thin layer over the runtime `Effect` enum that:
covers a quarter of variants, defaults to no-auth, lies about conservation,
silently no-ops half the prover input, and forks into three incompatible
"executable" types one of which (`CompoundTurn`) has no consumer.

The redesigned DSL is a four-layer tower —
**Intent → EffectPlan → SealedTurn → Turn** — where:
- Intent is small, declarative, and total.
- Lowering is deterministic, tested, and lives in one place.
- Authorization is a typestate; `Unchecked` is unrepresentable by default.
- Every one of the 42 runtime effect variants has a typed builder.
- Conservation is derived from effects, not declared by users.
- `CompoundTurn`, `SettlementAction`, and `RingTradeParticipant::settle_leg`
  fold into `Intent::RingSettlement` and `SettlementObserver`.
- The app-framework cannot construct unauthorized turns by default.

The bugs the audit flagged (findings 1, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14,
15, 18, 19, 20) are fixed by the redesign as direct consequences, not as
patches. The remaining findings (2, 11, 16, 17) are addressed by adjacent
work (Effect VM Shape A; the unbounded-growth fix in the engine) and noted
in §9.

The codebase is 2 days old. The breakage is welcome.
