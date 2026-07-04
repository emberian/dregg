//! `payable` — the production [`Settlement`] rail: each metered `(lease,
//! period)` charge becomes one real conserving `Effect::Transfer` turn,
//! submitted over an injected wire.
//!
//! A [`PayableSettlement`] settles a [`LeaseCharge`] by:
//!
//! 1. decoding the charge's payer / beneficiary / asset to kernel identities
//!    (64-hex cell ids — in the dregg value model an asset IS its issuer cell,
//!    `AssetId := token_id`), refusing malformed identities before any wire
//!    call;
//! 2. handing the payment terms to an injected [`PaySubmitter`] — the wire
//!    seam a dregg node client implements (sign + execute the transfer turn,
//!    e.g. a live-node client's submit-transfer over
//!    `POST /api/turns/submit`). The node's verified producer executes the ONE
//!    conserving kernel `Effect::Transfer` (per-asset Σδ = 0) and returns the
//!    on-chain turn hash;
//! 3. recording the settlement exactly-once per `(lease_id, period)`, with the
//!    on-chain turn hash readable back through
//!    [`Settlement::settled_turn_hash`] — the value a sealed product receipt
//!    (the receipt hex codec) threads into its `turn_receipt_hash` view link.
//!
//! The [`PaySubmitter`] seam is expressed in wire types (hex strings), so an
//! implementor links no dregg crate — a live-node client stays a plain network
//! client of the node process, and its `NodeApiClient` implements the seam in
//! a few lines.
//!
//! ## Named residual: the in-process `dregg-payable` desugar
//!
//! The payment SHOULD additionally resolve through breadstuffs'
//! `dregg_payable::resolve_pay` (the verified DFA route over the shared
//! `payable_descriptor`, the `Signature` cap gate, and the desugar to the
//! single conserving `Effect::Transfer`) before submission, so the client-side
//! desugar is the same verified code path the node runs. Linking it is
//! currently blocked at the workspace root: `dregg-turn`'s optional
//! `ark-serialize` requirement needs the breadstuffs `[patch.crates-io]` fork
//! replicated in the operated-layer root manifest (see the source durable manifest, the
//! BLOCKED RESIDUAL note, for the exact two patch lines). Until that lands the
//! desugar runs only node-side, behind the wire.

use std::collections::HashMap;
use std::sync::Mutex;

use crate::settle::{LeaseCharge, SettleError, SettleReceipt, Settlement};

/// Parse a 64-hex-char string into 32 bytes, or `None` if it is malformed —
/// the receipt/turn-hash hex codec (vendored: a self-contained validator, no
/// operated-layer dependency for two trivial helpers).
fn hex32(hex: &str) -> Option<[u8; 32]> {
    let bytes = hex.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let nibble = |b: u8| -> Option<u8> {
        match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            b'A'..=b'F' => Some(b - b'A' + 10),
            _ => None,
        }
    };
    let mut out = [0u8; 32];
    for (i, pair) in bytes.chunks(2).enumerate() {
        out[i] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Some(out)
}

/// A turn receipt hash parsed from its 64-hex-char wire form.
fn turn_hash_from_hex(hex: &str) -> Option<[u8; 32]> {
    hex32(hex)
}

/// The wire terms of one payment — what a [`PaySubmitter`] signs and executes
/// as a conserving transfer turn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PayTerms {
    /// The payer cell id (64-hex) — the `from` of the conserving transfer.
    pub from_hex: String,
    /// The beneficiary cell id (64-hex) — the `to` of the transfer.
    pub to_hex: String,
    /// The asset's issuer-cell id (64-hex) — the charge's `token_id`.
    pub asset_hex: String,
    /// The units to move.
    pub amount: u64,
    /// The auditable idempotency memo, `hosted-settle:<lease>:<period>` —
    /// the same key the settlement dedup uses, visible in the receipt log.
    pub memo: String,
}

/// What the wire returned for a submitted payment.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SubmittedPay {
    /// The on-chain turn-receipt hash (64-hex), when the node reported it.
    pub turn_hash_hex: Option<String>,
    /// The payer's post-transfer balance, when readable (`0` if not).
    pub payer_balance: i64,
    /// The beneficiary's post-transfer balance, when readable (`0` if not).
    pub beneficiary_balance: i64,
}

/// The wire seam a [`PayableSettlement`] submits payments through —
/// implemented by a node client (sign + execute the transfer turn) or a test
/// double. Expressed in hex wire types so an implementor links no dregg crate.
pub trait PaySubmitter: Send + Sync {
    /// Sign + execute the payment as a turn. `Err` means no turn committed
    /// (the settle is refused and NOT recorded — safe to retry).
    fn submit_pay(&self, terms: &PayTerms) -> Result<SubmittedPay, SettleError>;

    /// The real funded balance `holder_hex` (a 64-hex cell id) holds on this
    /// rail — the authoritative admission read. Fail-closed default: `0`
    /// (unknown ⇒ refuse); a submitter that can read a live balance overrides.
    fn funded_balance(&self, _holder_hex: &str) -> i64 {
        0
    }
}

/// The production [`Settlement`]: each charge is one conserving transfer turn
/// submitted over an injected [`PaySubmitter`]. Exactly-once per `(lease_id,
/// period)` in-process (the settle — dedup check, decode, submit, record — is
/// one critical section, so concurrent settles of the same period cannot
/// double-submit); cross-restart exactly-once is the submitter side's concern
/// (the node-API rail's durable write-ahead ledger).
pub struct PayableSettlement<S: PaySubmitter> {
    submitter: S,
    /// Optional `asset label -> issuer-cell id (64-hex)` aliases, for charges
    /// whose `asset` is a human label rather than a 64-hex token id.
    asset_aliases: HashMap<String, String>,
    /// `(lease_id, period) -> (receipt, on-chain turn hash)` — the
    /// exactly-once record.
    settled: Mutex<HashMap<(String, i64), (SettleReceipt, Option<[u8; 32]>)>>,
}

impl<S: PaySubmitter> PayableSettlement<S> {
    /// A settlement rail submitting through `submitter`.
    pub fn new(submitter: S) -> PayableSettlement<S> {
        PayableSettlement {
            submitter,
            asset_aliases: HashMap::new(),
            settled: Mutex::new(HashMap::new()),
        }
    }

    /// Register an asset alias: charges denominated in `label` resolve to the
    /// issuer-cell `asset_hex` (64-hex). A charge whose `asset` is already a
    /// 64-hex id needs no alias.
    pub fn with_asset(mut self, label: impl Into<String>, asset_hex: impl Into<String>) -> Self {
        self.asset_aliases.insert(label.into(), asset_hex.into());
        self
    }

    /// Resolve a charge's `asset` string to the issuer-cell id (64-hex): a
    /// registered alias, or already a 64-hex id. Malformed ⇒ refused.
    fn asset_hex(&self, asset: &str) -> Result<String, SettleError> {
        let candidate = self
            .asset_aliases
            .get(asset)
            .map(String::as_str)
            .unwrap_or(asset);
        if hex32(candidate).is_none() {
            return Err(SettleError::Backend(format!(
                "asset `{asset}` is neither a registered alias nor a 64-hex issuer-cell id"
            )));
        }
        Ok(candidate.to_string())
    }
}

/// Require `hex` to be a 64-hex cell id, naming `role` in the refusal.
fn require_cell_id(role: &str, hex: &str) -> Result<(), SettleError> {
    if hex32(hex).is_none() {
        return Err(SettleError::Backend(format!(
            "{role} `{hex}` is not a 64-hex cell id"
        )));
    }
    Ok(())
}

impl<S: PaySubmitter> Settlement for PayableSettlement<S> {
    fn settle(&self, charge: &LeaseCharge) -> Result<SettleReceipt, SettleError> {
        if charge.amount <= 0 {
            return Err(SettleError::NonPositiveAmount(charge.amount));
        }
        let amount = u64::try_from(charge.amount)
            .map_err(|_| SettleError::NonPositiveAmount(charge.amount))?;

        // One critical section across dedup + decode + submit + record, so a
        // concurrent settle of the same period cannot double-submit.
        let key = (charge.lease_id.clone(), charge.period);
        let mut settled = self.settled.lock().expect("settlement record poisoned");
        if let Some((prior, _)) = settled.get(&key) {
            if prior.amount != charge.amount || prior.asset != charge.asset {
                return Err(SettleError::Conflict {
                    lease_id: charge.lease_id.clone(),
                    period: charge.period,
                });
            }
            let mut replay = prior.clone();
            replay.replayed = true;
            return Ok(replay);
        }

        // Kernel identities, refused before any wire call.
        require_cell_id("payer", &charge.payer)?;
        require_cell_id("beneficiary", &charge.beneficiary)?;
        let asset_hex = self.asset_hex(&charge.asset)?;

        let terms = PayTerms {
            from_hex: charge.payer.clone(),
            to_hex: charge.beneficiary.clone(),
            asset_hex,
            amount,
            memo: format!("hosted-settle:{}:{}", charge.lease_id, charge.period),
        };
        let submitted = self.submitter.submit_pay(&terms)?;
        let turn_hash = submitted
            .turn_hash_hex
            .as_deref()
            .and_then(turn_hash_from_hex);

        let receipt = SettleReceipt {
            lease_id: charge.lease_id.clone(),
            period: charge.period,
            asset: charge.asset.clone(),
            amount: charge.amount,
            payer_balance: submitted.payer_balance,
            beneficiary_balance: submitted.beneficiary_balance,
            replayed: false,
        };
        settled.insert(key, (receipt.clone(), turn_hash));
        Ok(receipt)
    }

    fn settled_total(&self, lease_id: &str) -> i64 {
        self.settled
            .lock()
            .expect("settlement record poisoned")
            .iter()
            .filter(|((l, _), _)| l == lease_id)
            .map(|(_, (r, _))| r.amount)
            .sum()
    }

    /// The real on-chain reserve `holder` (a 64-hex cell id) holds, read
    /// through the submitter. Fail-closed: a non-cell-id holder or an
    /// unreadable balance is `0` (refuse admission).
    fn funded_balance(&self, _asset: &str, holder: &str) -> i64 {
        if hex32(holder).is_none() {
            return 0;
        }
        self.submitter.funded_balance(holder)
    }

    /// The recorded on-chain turn hash for a settled `(lease_id, period)`.
    fn settled_turn_hash(&self, lease_id: &str, period: i64) -> Option<[u8; 32]> {
        self.settled
            .lock()
            .expect("settlement record poisoned")
            .get(&(lease_id.to_string(), period))
            .and_then(|(_, h)| *h)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    const PAYER: &str = "1111111111111111111111111111111111111111111111111111111111111111";
    const BENEF: &str = "2222222222222222222222222222222222222222222222222222222222222222";
    const ASSET: &str = "3333333333333333333333333333333333333333333333333333333333333333";
    const TURN: &str = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";

    /// A wire double: records every submitted term set, answers with a fixed
    /// turn hash and balances.
    struct MockWire {
        submits: AtomicUsize,
        terms: Mutex<Vec<PayTerms>>,
    }

    impl MockWire {
        fn new() -> MockWire {
            MockWire {
                submits: AtomicUsize::new(0),
                terms: Mutex::new(Vec::new()),
            }
        }
    }

    impl PaySubmitter for MockWire {
        fn submit_pay(&self, terms: &PayTerms) -> Result<SubmittedPay, SettleError> {
            self.submits.fetch_add(1, Ordering::SeqCst);
            self.terms.lock().unwrap().push(terms.clone());
            Ok(SubmittedPay {
                turn_hash_hex: Some(TURN.to_string()),
                payer_balance: 93,
                beneficiary_balance: 7,
            })
        }
        fn funded_balance(&self, _holder_hex: &str) -> i64 {
            100
        }
    }

    fn charge(lease: &str, period: i64, amount: i64) -> LeaseCharge {
        LeaseCharge::new(PAYER, BENEF, ASSET, lease, period, amount)
    }

    #[test]
    fn settle_submits_and_records_the_turn_hash() {
        let rail = PayableSettlement::new(MockWire::new());
        let r = rail.settle(&charge("lease-1", 1, 7)).expect("settle");
        assert!(!r.replayed);
        assert_eq!(r.payer_balance, 93);
        assert_eq!(r.beneficiary_balance, 7);

        // The wire saw exactly the decoded terms, memo-keyed.
        let terms = rail.submitter.terms.lock().unwrap();
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0].from_hex, PAYER);
        assert_eq!(terms[0].to_hex, BENEF);
        assert_eq!(terms[0].asset_hex, ASSET);
        assert_eq!(terms[0].amount, 7);
        assert_eq!(terms[0].memo, "hosted-settle:lease-1:1");
        drop(terms);

        // The on-chain turn hash is recorded and readable — the receipt-contract
        // thread-through.
        assert_eq!(
            rail.settled_turn_hash("lease-1", 1),
            turn_hash_from_hex(TURN)
        );
        assert_eq!(rail.settled_turn_hash("lease-1", 2), None);
    }

    #[test]
    fn settle_is_exactly_once_per_period() {
        let rail = PayableSettlement::new(MockWire::new());
        let first = rail.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(!first.replayed);
        let again = rail.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(again.replayed);
        // Only ONE turn went over the wire.
        assert_eq!(rail.submitter.submits.load(Ordering::SeqCst), 1);
        assert_eq!(rail.settled_total("lease-1"), 5);
    }

    #[test]
    fn same_key_different_terms_is_a_conflict() {
        let rail = PayableSettlement::new(MockWire::new());
        rail.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(matches!(
            rail.settle(&charge("lease-1", 1, 9)),
            Err(SettleError::Conflict { .. })
        ));
    }

    #[test]
    fn non_cell_id_identities_are_refused_before_the_wire() {
        let rail = PayableSettlement::new(MockWire::new());
        let bad = LeaseCharge::new("not-a-cell", BENEF, ASSET, "lease-1", 1, 5);
        assert!(matches!(rail.settle(&bad), Err(SettleError::Backend(_))));
        let bad_asset = LeaseCharge::new(PAYER, BENEF, "DREGG", "lease-1", 1, 5);
        assert!(matches!(
            rail.settle(&bad_asset),
            Err(SettleError::Backend(_))
        ));
        assert_eq!(rail.submitter.submits.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn asset_aliases_resolve_to_the_issuer_cell() {
        let rail = PayableSettlement::new(MockWire::new()).with_asset("DREGG", ASSET);
        let c = LeaseCharge::new(PAYER, BENEF, "DREGG", "lease-1", 1, 5);
        rail.settle(&c).expect("aliased asset settles");
        let terms = rail.submitter.terms.lock().unwrap();
        assert_eq!(terms[0].asset_hex, ASSET);
    }

    #[test]
    fn funded_balance_is_fail_closed() {
        let rail = PayableSettlement::new(MockWire::new());
        assert_eq!(rail.funded_balance("DREGG", PAYER), 100);
        assert_eq!(rail.funded_balance("DREGG", "not-a-cell"), 0);
    }

    #[test]
    fn a_wire_refusal_records_nothing() {
        struct RefusingWire;
        impl PaySubmitter for RefusingWire {
            fn submit_pay(&self, _t: &PayTerms) -> Result<SubmittedPay, SettleError> {
                Err(SettleError::Backend("node said no".into()))
            }
        }
        let rail = PayableSettlement::new(RefusingWire);
        assert!(matches!(
            rail.settle(&charge("lease-1", 1, 5)),
            Err(SettleError::Backend(_))
        ));
        // Nothing recorded — the period is retryable.
        assert_eq!(rail.settled_total("lease-1"), 0);
        assert_eq!(rail.settled_turn_hash("lease-1", 1), None);
    }
}
