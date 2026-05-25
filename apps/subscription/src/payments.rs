//! Payment executor: collects auto-debit turns for subscribers and applies
//! them to real balance state in batches per epoch.
//!
//! # Why batches?
//!
//! Each epoch, dozens or hundreds of subscribers owe their creators a small
//! amount. Settling them one-at-a-time is wasteful. The executor:
//!
//! 1. **Collects** all due debits as `ClientTurnRequest`s (one per
//!    subscription).
//! 2. **Executes** the whole batch against the in-memory `BalanceLedger`,
//!    moving numbers from subscriber accounts into creator accounts.
//! 3. **Caps** each debit at `auth.max_per_epoch` and refuses to debit any
//!    asset other than `auth.asset_id`.
//!
//! # What this is NOT
//!
//! This is not a STARK-proven settlement — the `BatchExecution.proof` field
//! is `None`. A future version would generate a proof over the (pre_balances,
//! debits, post_balances) tuple. See REVIEW[P2].

use std::collections::HashMap;

use pyana_app_framework::batch_executor::{BatchExecution, BatchExecutor, ClientTurnRequest};
use pyana_types::PublicKey;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::subscriber::SubscriberRegistry;

/// One pending debit turn, decoded from a `ClientTurnRequest::turn_bytes`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DebitTurn {
    /// Subscriber being debited.
    pub subscriber: PublicKey,
    /// Creator receiving the funds.
    pub creator: PublicKey,
    /// Tier id the debit applies to (informational; the canonical price
    /// comes from `amount`).
    pub tier_id: String,
    /// Asset id (must match the subscriber's authorization).
    pub asset_id: u64,
    /// Amount being debited (must be <= authorization's max_per_epoch).
    pub amount: u64,
    /// Epoch at which the debit applies.
    pub epoch: u64,
}

/// Simple per-asset balance ledger.
///
/// Maps `(account_pubkey, asset_id) -> balance`. Debits decrement the
/// subscriber's balance and increment the creator's; both must succeed for
/// the debit to count, or the transfer is rolled back.
#[derive(Default, Debug, Clone, Serialize, Deserialize)]
pub struct BalanceLedger {
    pub balances: HashMap<(PublicKey, u64), u64>,
}

impl BalanceLedger {
    pub fn new() -> Self {
        Self::default()
    }

    /// Set a balance (used to seed accounts in tests/init).
    pub fn set(&mut self, account: PublicKey, asset_id: u64, amount: u64) {
        self.balances.insert((account, asset_id), amount);
    }

    pub fn balance(&self, account: PublicKey, asset_id: u64) -> u64 {
        self.balances
            .get(&(account, asset_id))
            .copied()
            .unwrap_or(0)
    }

    /// Atomic transfer. Returns `Err` if `from` has insufficient balance,
    /// in which case NO change is made.
    pub fn transfer(
        &mut self,
        from: PublicKey,
        to: PublicKey,
        asset_id: u64,
        amount: u64,
    ) -> Result<(), PaymentsError> {
        let from_bal = self.balance(from, asset_id);
        if from_bal < amount {
            return Err(PaymentsError::InsufficientBalance {
                account: from,
                asset_id,
                have: from_bal,
                need: amount,
            });
        }
        self.balances.insert((from, asset_id), from_bal - amount);
        let to_bal = self.balance(to, asset_id);
        self.balances
            .insert((to, asset_id), to_bal.saturating_add(amount));
        Ok(())
    }
}

#[derive(Debug, Error)]
pub enum PaymentsError {
    #[error("no auto-debit authorization on file for subscriber")]
    NoAuthorization,
    #[error("debit asset {requested} does not match authorized asset {authorized} for subscriber")]
    WrongAsset { authorized: u64, requested: u64 },
    #[error("debit amount {requested} exceeds per-epoch limit {limit} for subscriber")]
    ExceedsLimit { limit: u64, requested: u64 },
    #[error("account {account:?} has {have} of asset {asset_id}, needs {need}")]
    InsufficientBalance {
        account: PublicKey,
        asset_id: u64,
        have: u64,
        need: u64,
    },
    #[error("malformed turn bytes: {0}")]
    Malformed(String),
    #[error("authorization expired (not_after={0})")]
    Expired(i64),
}

/// Payment batch executor.
pub struct PaymentExecutor {
    /// Pending turns waiting for the next `collect_batch` call.
    pending: Vec<ClientTurnRequest>,
    /// Authoritative balance state.
    pub ledger: BalanceLedger,
    /// Per-(subscriber, epoch) debit accumulator. Used to enforce
    /// `max_per_epoch` even when the executor sees multiple turns for the
    /// same subscriber in the same epoch.
    pub debited_this_epoch: HashMap<(PublicKey, u64), u64>,
    /// Receipts of successfully applied debits (for audit / reporting).
    pub receipts: Vec<DebitReceipt>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DebitReceipt {
    pub subscriber: PublicKey,
    pub creator: PublicKey,
    pub asset_id: u64,
    pub amount: u64,
    pub epoch: u64,
}

impl Default for PaymentExecutor {
    fn default() -> Self {
        Self::new()
    }
}

impl PaymentExecutor {
    pub fn new() -> Self {
        Self {
            pending: Vec::new(),
            ledger: BalanceLedger::new(),
            debited_this_epoch: HashMap::new(),
            receipts: Vec::new(),
        }
    }

    /// Enqueue a debit turn for the next batch.
    ///
    /// This does NOT yet check the authorization — that happens in
    /// `apply_batch` against the registry. The reason is that turns may be
    /// enqueued by an HTTP handler that doesn't hold the registry lock; the
    /// authorization check is the source of truth.
    pub fn enqueue_debit(&mut self, debit: DebitTurn) -> Result<(), PaymentsError> {
        let turn_bytes =
            serde_json::to_vec(&debit).map_err(|e| PaymentsError::Malformed(e.to_string()))?;
        self.pending.push(ClientTurnRequest {
            client: pyana_types::CellId(debit.subscriber.0),
            turn_bytes,
            deadline_height: Some(debit.epoch),
        });
        Ok(())
    }

    /// Scan the registry and enqueue this epoch's debit turns.
    ///
    /// One turn per (subscriber, creator, tier) that:
    /// - has an active subscription,
    /// - has an active auto-debit authorization,
    /// - and where the tier's `price_per_epoch` is > 0.
    ///
    /// Returns the number of turns enqueued.
    pub fn schedule_epoch(
        &mut self,
        registry: &SubscriberRegistry,
        creators: &[(PublicKey, &crate::creator::Creator)],
        epoch: u64,
    ) -> usize {
        let mut count = 0;
        for sub in &registry.subscriptions {
            if !sub.active {
                continue;
            }
            let Some(auth) = registry.debit_authorizations.get(&sub.subscriber) else {
                continue;
            };
            let Some((_, creator)) = creators.iter().find(|(pk, _)| *pk == sub.creator) else {
                continue;
            };
            let Some(tier) = creator.tier(&sub.tier_id) else {
                continue;
            };
            if tier.price_per_epoch == 0 {
                continue; // free tier
            }
            if tier.asset_id != auth.asset_id {
                continue; // delegation does not authorize debits in this asset
            }
            let amount = tier.price_per_epoch.min(auth.max_per_epoch);
            let debit = DebitTurn {
                subscriber: sub.subscriber,
                creator: sub.creator,
                tier_id: sub.tier_id.clone(),
                asset_id: tier.asset_id,
                amount,
                epoch,
            };
            if self.enqueue_debit(debit).is_ok() {
                count += 1;
            }
        }
        count
    }

    /// Apply a batch of collected debits against the ledger.
    ///
    /// For each turn:
    /// - Look up the subscriber's `DebitAuthorization`.
    /// - Reject if no authorization, wrong asset, or amount > `max_per_epoch`
    ///   (cumulative for this epoch).
    /// - Reject if `expires_at_unix_secs` is in the past.
    /// - Otherwise, `BalanceLedger::transfer(subscriber -> creator)`.
    ///
    /// Per-turn failures do not abort the batch — they just skip that turn.
    /// Returns the receipts of successfully applied debits.
    pub fn apply_batch(
        &mut self,
        registry: &SubscriberRegistry,
        batch: &[ClientTurnRequest],
    ) -> Vec<DebitReceipt> {
        let now_secs = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);

        let mut applied = Vec::new();
        for req in batch {
            let Ok(debit) = serde_json::from_slice::<DebitTurn>(&req.turn_bytes) else {
                continue;
            };
            let Some(auth) = registry.debit_authorizations.get(&debit.subscriber) else {
                continue;
            };
            // Expiry.
            if let Some(not_after) = auth.expires_at_unix_secs {
                if not_after <= now_secs {
                    continue;
                }
            }
            // Asset binding.
            if debit.asset_id != auth.asset_id {
                continue;
            }
            // Per-epoch cumulative limit.
            let prior = *self
                .debited_this_epoch
                .get(&(debit.subscriber, debit.epoch))
                .unwrap_or(&0);
            let new_cum = prior.saturating_add(debit.amount);
            if new_cum > auth.max_per_epoch {
                continue;
            }
            // Move balances.
            if self
                .ledger
                .transfer(
                    debit.subscriber,
                    debit.creator,
                    debit.asset_id,
                    debit.amount,
                )
                .is_err()
            {
                continue;
            }
            self.debited_this_epoch
                .insert((debit.subscriber, debit.epoch), new_cum);
            let receipt = DebitReceipt {
                subscriber: debit.subscriber,
                creator: debit.creator,
                asset_id: debit.asset_id,
                amount: debit.amount,
                epoch: debit.epoch,
            };
            applied.push(receipt.clone());
            self.receipts.push(receipt);
        }
        applied
    }

    /// Programmatic debit (bypasses turn serialization) used by tests and
    /// direct callers. Runs the exact same authorization checks as
    /// `apply_batch`.
    pub fn debit(
        &mut self,
        registry: &SubscriberRegistry,
        debit: DebitTurn,
    ) -> Result<DebitReceipt, PaymentsError> {
        let auth = registry
            .debit_authorizations
            .get(&debit.subscriber)
            .ok_or(PaymentsError::NoAuthorization)?;

        let now_secs = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        if let Some(not_after) = auth.expires_at_unix_secs {
            if not_after <= now_secs {
                return Err(PaymentsError::Expired(not_after));
            }
        }
        if debit.asset_id != auth.asset_id {
            return Err(PaymentsError::WrongAsset {
                authorized: auth.asset_id,
                requested: debit.asset_id,
            });
        }
        let prior = *self
            .debited_this_epoch
            .get(&(debit.subscriber, debit.epoch))
            .unwrap_or(&0);
        let new_cum = prior.saturating_add(debit.amount);
        if new_cum > auth.max_per_epoch {
            return Err(PaymentsError::ExceedsLimit {
                limit: auth.max_per_epoch,
                requested: new_cum,
            });
        }
        self.ledger.transfer(
            debit.subscriber,
            debit.creator,
            debit.asset_id,
            debit.amount,
        )?;
        self.debited_this_epoch
            .insert((debit.subscriber, debit.epoch), new_cum);
        let receipt = DebitReceipt {
            subscriber: debit.subscriber,
            creator: debit.creator,
            asset_id: debit.asset_id,
            amount: debit.amount,
            epoch: debit.epoch,
        };
        self.receipts.push(receipt.clone());
        Ok(receipt)
    }
}

#[derive(Debug)]
pub struct ExecutorError(pub String);

impl BatchExecutor for PaymentExecutor {
    type Error = ExecutorError;

    fn collect_batch(&mut self, max_size: usize) -> Vec<ClientTurnRequest> {
        let n = max_size.min(self.pending.len());
        self.pending.drain(..n).collect()
    }

    /// Compute the batch id from turn bytes. Does NOT apply the batch — the
    /// HTTP path calls `apply_batch` separately because it needs the registry.
    fn execute_batch(
        &mut self,
        batch: Vec<ClientTurnRequest>,
    ) -> Result<BatchExecution, ExecutorError> {
        let mut hasher = blake3::Hasher::new();
        for req in &batch {
            hasher.update(&req.turn_bytes);
        }
        Ok(BatchExecution {
            batch_id: *hasher.finalize().as_bytes(),
            turn_count: batch.len(),
            proof: None,
        })
    }
}

// REVIEW[P2]: `execute_batch` and `apply_batch` are split because the
// `BatchExecutor` trait does not give us a way to thread the
// `SubscriberRegistry` (or any external state) into the call. The result is
// that `BatchExecution.turn_count` reports the size of the batch as
// collected, not the number of debits that actually moved balances. The
// lending app has the same pattern with a `// REVIEW[P2]:` marker — until the
// trait grows associated context, callers must read `apply_batch`'s return
// value for the real count.

// REVIEW[P3]: no STARK proof is produced. A future version would generate a
// proof over `(pre_balances, debits, post_balances)`.

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::creator::{Creator, Tier};
    use crate::subscriber::{SubscriberRegistry, deterministic_wallet};
    use pyana_sdk::Attenuation;
    use pyana_token::BudgetSpec;

    fn wallet(seed: u8) -> pyana_sdk::AgentCipherclerk {
        let mut s = [0u8; 32];
        s[0] = seed;
        s[31] = seed.wrapping_mul(13);
        deterministic_wallet(s)
    }

    fn install_debit_auth(
        reg: &mut SubscriberRegistry,
        subscriber: &mut pyana_sdk::AgentCipherclerk,
        executor_w: &mut pyana_sdk::AgentCipherclerk,
        asset_id: u64,
        max_per_epoch: u64,
    ) {
        let token = subscriber.mint_token(&[7u8; 32], "subscription-debit");
        let restrictions = Attenuation {
            budget: Some(BudgetSpec {
                id: "subscription:debit".into(),
                parent_id: None,
                class: format!("asset:{asset_id}"),
                limit: max_per_epoch,
                window: Some("epoch".into()),
            }),
            not_after: Some(i64::MAX),
            ..Default::default()
        };
        let env = subscriber
            .delegate(&token, &executor_w.public_key(), &restrictions)
            .unwrap();
        reg.receive_debit_delegation(executor_w, subscriber.public_key(), env)
            .unwrap();
    }

    #[test]
    fn debit_moves_balance() {
        let mut reg = SubscriberRegistry::new();
        let mut alice = wallet(1);
        let bob = wallet(2);
        let mut executor_w = wallet(3);

        install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 1000);

        let mut exec = PaymentExecutor::new();
        exec.ledger.set(alice.public_key(), 1, 500);
        exec.ledger.set(bob.public_key(), 1, 0);

        let d = DebitTurn {
            subscriber: alice.public_key(),
            creator: bob.public_key(),
            tier_id: "vip".into(),
            asset_id: 1,
            amount: 100,
            epoch: 0,
        };
        exec.debit(&reg, d).expect("debit should succeed");

        // Numbers must move.
        assert_eq!(exec.ledger.balance(alice.public_key(), 1), 400);
        assert_eq!(exec.ledger.balance(bob.public_key(), 1), 100);
    }

    /// ADVERSARIAL: debit an asset NOT in the delegation's restrictions ->
    /// rejected.
    #[test]
    fn debit_wrong_asset_rejected() {
        let mut reg = SubscriberRegistry::new();
        let mut alice = wallet(4);
        let bob = wallet(5);
        let mut executor_w = wallet(6);

        // Authorize ONLY asset 1.
        install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 1000);

        let mut exec = PaymentExecutor::new();
        exec.ledger.set(alice.public_key(), 7, 500);

        let d = DebitTurn {
            subscriber: alice.public_key(),
            creator: bob.public_key(),
            tier_id: "vip".into(),
            asset_id: 7, // not authorized
            amount: 10,
            epoch: 0,
        };
        let r = exec.debit(&reg, d);
        assert!(matches!(
            r,
            Err(PaymentsError::WrongAsset {
                authorized: 1,
                requested: 7
            })
        ));
        // Balance unchanged.
        assert_eq!(exec.ledger.balance(alice.public_key(), 7), 500);
    }

    /// ADVERSARIAL: debit > max_per_epoch -> rejected.
    #[test]
    fn debit_exceeds_limit_rejected() {
        let mut reg = SubscriberRegistry::new();
        let mut alice = wallet(7);
        let bob = wallet(8);
        let mut executor_w = wallet(9);

        // Authorize asset 1 up to 100 per epoch.
        install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 100);

        let mut exec = PaymentExecutor::new();
        exec.ledger.set(alice.public_key(), 1, 1_000);

        let d = DebitTurn {
            subscriber: alice.public_key(),
            creator: bob.public_key(),
            tier_id: "vip".into(),
            asset_id: 1,
            amount: 250, // over the limit
            epoch: 0,
        };
        let r = exec.debit(&reg, d);
        assert!(matches!(
            r,
            Err(PaymentsError::ExceedsLimit {
                limit: 100,
                requested: 250
            })
        ));
        assert_eq!(exec.ledger.balance(alice.public_key(), 1), 1_000);
    }

    /// ADVERSARIAL: cumulative debits within one epoch must not exceed limit.
    #[test]
    fn debit_cumulative_limit_enforced() {
        let mut reg = SubscriberRegistry::new();
        let mut alice = wallet(10);
        let bob = wallet(11);
        let mut executor_w = wallet(12);

        install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 100);

        let mut exec = PaymentExecutor::new();
        exec.ledger.set(alice.public_key(), 1, 1_000);

        // First debit: 70/100, OK.
        exec.debit(
            &reg,
            DebitTurn {
                subscriber: alice.public_key(),
                creator: bob.public_key(),
                tier_id: "vip".into(),
                asset_id: 1,
                amount: 70,
                epoch: 5,
            },
        )
        .unwrap();
        // Second debit: 70+50 = 120 > 100, must be rejected.
        let r = exec.debit(
            &reg,
            DebitTurn {
                subscriber: alice.public_key(),
                creator: bob.public_key(),
                tier_id: "vip".into(),
                asset_id: 1,
                amount: 50,
                epoch: 5,
            },
        );
        assert!(matches!(
            r,
            Err(PaymentsError::ExceedsLimit { limit: 100, .. })
        ));
        assert_eq!(exec.ledger.balance(alice.public_key(), 1), 930);
    }

    /// Debits in DIFFERENT epochs each get a full quota.
    #[test]
    fn debit_quota_resets_across_epochs() {
        let mut reg = SubscriberRegistry::new();
        let mut alice = wallet(13);
        let bob = wallet(14);
        let mut executor_w = wallet(15);

        install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 100);

        let mut exec = PaymentExecutor::new();
        exec.ledger.set(alice.public_key(), 1, 1_000);

        for epoch in 0..3 {
            exec.debit(
                &reg,
                DebitTurn {
                    subscriber: alice.public_key(),
                    creator: bob.public_key(),
                    tier_id: "vip".into(),
                    asset_id: 1,
                    amount: 100,
                    epoch,
                },
            )
            .unwrap();
        }
        assert_eq!(exec.ledger.balance(alice.public_key(), 1), 700);
        assert_eq!(exec.ledger.balance(bob.public_key(), 1), 300);
    }

    /// No authorization -> rejected.
    #[test]
    fn debit_no_auth_rejected() {
        let reg = SubscriberRegistry::new();
        let alice = wallet(16);
        let bob = wallet(17);

        let mut exec = PaymentExecutor::new();
        exec.ledger.set(alice.public_key(), 1, 500);

        let r = exec.debit(
            &reg,
            DebitTurn {
                subscriber: alice.public_key(),
                creator: bob.public_key(),
                tier_id: "vip".into(),
                asset_id: 1,
                amount: 10,
                epoch: 0,
            },
        );
        assert!(matches!(r, Err(PaymentsError::NoAuthorization)));
        assert_eq!(exec.ledger.balance(alice.public_key(), 1), 500);
    }

    /// Insufficient balance is its own error, not a silent skip.
    #[test]
    fn debit_insufficient_balance_rejected() {
        let mut reg = SubscriberRegistry::new();
        let mut alice = wallet(18);
        let bob = wallet(19);
        let mut executor_w = wallet(20);

        install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 1000);
        let mut exec = PaymentExecutor::new();
        exec.ledger.set(alice.public_key(), 1, 5);

        let r = exec.debit(
            &reg,
            DebitTurn {
                subscriber: alice.public_key(),
                creator: bob.public_key(),
                tier_id: "vip".into(),
                asset_id: 1,
                amount: 100,
                epoch: 0,
            },
        );
        assert!(matches!(
            r,
            Err(PaymentsError::InsufficientBalance {
                have: 5,
                need: 100,
                ..
            })
        ));
    }

    /// Full batch path: schedule, collect, apply.
    #[test]
    fn schedule_collect_apply_round_trip() {
        let mut reg = SubscriberRegistry::new();
        let mut alice = wallet(21);
        let creator_w = wallet(22);
        let mut executor_w = wallet(23);
        reg.register_subscriber(alice.public_key(), [9u8; 32]);

        install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 1000);

        // Build the creator + a tier with price 50.
        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier {
            id: "vip".into(),
            label: "VIP".into(),
            price_per_epoch: 50,
            asset_id: 1,
            credential_issuer: None,
        });
        // Subscribe Alice.
        reg.subscribe(
            alice.public_key(),
            creator_w.public_key(),
            creator.tier("vip").unwrap(),
            None,
        )
        .unwrap();

        let mut exec = PaymentExecutor::new();
        exec.ledger.set(alice.public_key(), 1, 500);

        let creators = vec![(creator_w.public_key(), &creator)];
        let n = exec.schedule_epoch(&reg, &creators, 0);
        assert_eq!(n, 1);

        let batch = exec.collect_batch(10);
        assert_eq!(batch.len(), 1);

        let applied = exec.apply_batch(&reg, &batch);
        assert_eq!(applied.len(), 1);
        assert_eq!(applied[0].amount, 50);
        assert_eq!(exec.ledger.balance(alice.public_key(), 1), 450);
        assert_eq!(exec.ledger.balance(creator_w.public_key(), 1), 50);
    }
}
