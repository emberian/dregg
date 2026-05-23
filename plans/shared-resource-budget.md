# Shared Resource Budget: Generalizing Stingray Bounded Counters

## Status: Implemented (coord/src/shared_budget.rs)

## 1. Analysis: Can BudgetCoordinator Be Parameterized?

**Answer: No structural changes needed, but a new type is cleaner.**

The core math is identical: `ceiling = balance * (f+1) / (2f+1)`. The difference is semantic, not algorithmic:

| Dimension | BudgetCoordinator | SharedResourceBudget |
|-----------|-------------------|----------------------|
| What is distributed | One agent's budget | One resource's balance |
| Distributed to whom | Silos (nodes) | Agents (participants) |
| BFT threshold | 3f+1 silos | 2f+1 agents |
| Rebalance trigger | Periodic / exhaustion | Epoch close / exhaustion |
| Credits during epoch | N/A (balance is static) | Deposits increase balance |
| Fast unlock needed? | Yes (2PC abort) | Not directly (no 2PC for shared debits) |
| SpendingCertificate | Silo signs with Ed25519 | Agent's blocklace blocks serve as proof |

A wrapper or parameterized generic over BudgetCoordinator would obscure these differences. The new `SharedResourceBudget` type is ~150 lines of core logic (reusing the same formula) with clean semantics.

## 2. Who Is the Coordinator?

For a shared AMM pool, the coordinator is the **ordering node set** that the resource owner designated:

- **Not the pool cell itself** (cells are passive data, don't run code).
- **Not agents themselves** (they're the spenders, not arbiters).
- **Ordering nodes** (they track per-agent allowances and run rebalancing).

However, for peer-to-peer operation without ordering nodes, the **blocklace itself** can serve as the coordinator: each agent's virtual chain records their debits, and any observer can compute totals. The `sync_from_blocklace()` method supports this mode.

## 3. Dynamic Allowances

Solution implemented:
1. Allowances computed from **last known balance at epoch start** (stable during epoch).
2. Credits (deposits) tracked separately via `credit()`, increase `total_balance` immediately.
3. Allowance ceilings only change at rebalance (keeps the hot path simple).
4. Early rebalance can be triggered on allowance exhaustion.

Allowances intentionally DO NOT auto-adjust mid-epoch. This maintains the invariant that the bounded counter math holds: if ceilings changed mid-flight, in-progress debits could violate the safety bound.

## 4. Integration with COD Insights

| COD Concept | SharedResourceBudget Equivalent |
|-------------|----------------------------------|
| Close epoch | `rebalance()` |
| Open epoch | `distribute_allowances()` (implicit in rebalance) |
| Debit check | `try_debit()` (pre-allocated, not reactive) |
| Overspending detection | `is_overspent()` |
| Escalation | Return `AllowanceExhausted` -> caller escalates to Tier 3 |

Hybrid approach achieved:
- **Fast path** (COD-like): `try_debit()` is local, O(1), no coordination.
- **Reactive fallback**: when `is_overspent()` returns true or an agent hits `AllowanceExhausted`, escalate to Tier 3 ordering for conflict resolution.
- **Epoch boundaries** = COD close/open = Stingray rebalance. Same pattern.

## 5. Fast-Path: Eliminating the Lock Round

Current fast-path for multi-cell turns requires 2f+1 lock signatures. With bounded counters:

- **Within allowance**: agent debits locally, no lock needed, no network round trips.
- **Lock round eliminated for**: all debits that fit within the pre-allocated ceiling.
- **Lock round still needed for**: debits that exceed a single agent's allowance (these escalate to Tier 3 anyway).

Net effect: most shared-resource operations (small swaps, routine payments from shared accounts) hit the bounded-counter fast path. Only large operations that would exhaust the ceiling need coordination.

## 6. API Surface (Implemented)

```rust
// Create budget for a shared resource.
SharedResourceBudget::new(resource, balance, participants, f) -> Result<Self, Error>

// Hot path: agent debits locally.
budget.try_debit(agent, amount, digest) -> Result<(), SharedBudgetError>

// Check remaining allowance.
budget.remaining(&agent) -> Option<u64>

// Detect overspending.
budget.is_overspent() -> bool

// Record deposits.
budget.credit(amount)

// Epoch close.
budget.rebalance(reports, require_all) -> Result<u64, SharedBudgetError>

// Dynamic membership.
budget.add_participant(agent) -> Result<(), SharedBudgetError>
budget.remove_participant(&agent) -> Result<(), SharedBudgetError>

// Derive state from blocklace.
budget.sync_from_blocklace(&HashMap<ParticipantId, u64>)
```

## 7. Blocklace Composition

The bounded counter IS derivable from blocklace state:

1. Each agent's blocks in the blocklace contain their spending against shared resources (encoded in block payloads).
2. `sync_from_blocklace()` accepts a map of observed debits per agent and updates allowance states accordingly.
3. At rebalance time, the coordinator sums debits visible in the blocklace rather than requiring separate certificate messages.
4. This means the blocklace IS the spending record -- no separate accounting needed.

Equivocation detection (from the blocklace) directly catches Byzantine agents who try to double-spend: two incomparable blocks from the same agent against the same resource = proof of misbehavior.

## 8. Turn Executor Integration (Future Work)

To wire this into the execution path:

```rust
// In TurnExecutor, before executing a shared-resource effect:
if let Some(shared_budgets) = &self.shared_budgets {
    let budget = shared_budgets.get(&resource_id)?;
    budget.try_debit(agent, amount, digest)?;
    // If AllowanceExhausted -> reject turn, signal need for rebalance
}
```

This parallels the existing `BudgetGate` pattern but operates on a per-resource basis rather than per-agent-silo.

## 9. Safety Argument

With n participants, f Byzantine, ceiling = B * (f+1) / (2f+1):

- Maximum total allocation across all agents: n * ceiling
- Worst case (all agents spend full ceiling): n * B * (f+1) / (2f+1)
- Maximum overspend by Byzantine agents alone: f * ceiling = f * B * (f+1) / (2f+1)
- For f=1, n=3: max Byzantine overspend = B * 2/3 (bounded, detectable at rebalance)

The key: honest agents (at least n-f) will truthfully report at rebalance. The coordinator reconciles and detects any excess. Byzantine agents cannot cause undetectable loss beyond f * ceiling.

## 10. What Was NOT Implemented (Deferred)

- **Signature verification on spending reports** (rebalance currently trusts report values; production needs Ed25519 attestation like BudgetCoordinator's SpendingCertificate).
- **Tier 3 escalation protocol** (what happens AFTER `is_overspent()` returns true -- needs Cordial Miners ordering integration).
- **Per-resource BudgetGate in TurnExecutor** (the turn-crate integration point).
- **Allowance expansion on credit** (currently credits only take effect at rebalance; could optimize with mid-epoch expansion notification).
