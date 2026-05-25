//! Integration test: cipherclerk receipt chain integrity (audit #77).
//!
//! Audit finding #77 (now closed): `append_receipt` previously silently
//! rewrote the `previous_receipt_hash` field of any incoming receipt to the
//! cipherclerk's own chain head, regardless of what the caller supplied. This
//! meant that two honest nodes could diverge for the same agent without any
//! observable signal — cipherclerk's chain disagreed with the federation's
//! chain.
//!
//! **Strict-mode fix** (this file): `append_receipt` now returns
//! `Result<(), ChainAppendError>` and rejects any receipt whose
//! `previous_receipt_hash` does not match the cipherclerk's current head.
//! Genesis-claims against a non-empty chain are also rejected. Honest steady-
//! state callers see no behavioral change; fork conditions become observable.

mod common;

use pyana_turn::verify_receipt_chain;

// ---------------------------------------------------------------------------
// 1. Happy-path chain of 3
// ---------------------------------------------------------------------------

/// Three receipts appended in order: verify the chain links correctly and
/// `verify_receipt_chain` accepts it.
#[test]
fn receipt_chain_of_three_links_correctly() {
    let mut cclerk = common::cclerk_from_label("chain-of-three");
    let cell = cclerk.cell_id("test");

    // Genesis receipt: previous_receipt_hash = None.
    let r1 = common::mock_receipt(cell, [1u8; 32], [2u8; 32]);
    cclerk.append_receipt(r1).unwrap();

    // Subsequent receipts must carry the correct prev hash (strict mode).
    let prev1 = cclerk.receipt_head().unwrap().receipt_hash();
    let r2 = common::mock_receipt_with_prev(cell, [2u8; 32], [3u8; 32], Some(prev1));
    cclerk.append_receipt(r2).unwrap();

    let prev2 = cclerk.receipt_head().unwrap().receipt_hash();
    let r3 = common::mock_receipt_with_prev(cell, [3u8; 32], [4u8; 32], Some(prev2));
    cclerk.append_receipt(r3).unwrap();

    assert_eq!(cclerk.receipt_chain_length(), 3);

    let chain = cclerk.receipt_chain();

    // Genesis has no predecessor.
    assert_eq!(chain[0].previous_receipt_hash, None);

    // Each subsequent receipt links back to the previous receipt's hash.
    assert_eq!(
        chain[1].previous_receipt_hash,
        Some(chain[0].receipt_hash()),
        "receipt[1].previous must be hash(receipt[0])"
    );
    assert_eq!(
        chain[2].previous_receipt_hash,
        Some(chain[1].receipt_hash()),
        "receipt[2].previous must be hash(receipt[1])"
    );

    // The external verifier must accept the chain.
    assert!(
        verify_receipt_chain(chain).is_ok(),
        "verify_receipt_chain must accept a correctly-linked chain"
    );

    // verify_own_chain must also pass.
    assert!(cclerk.verify_own_chain().is_ok());
}

// ---------------------------------------------------------------------------
// 2. Audit #77: wrong prev-hash supplied by caller is silently rewritten
// ---------------------------------------------------------------------------

/// AUDIT #77 CLOSURE TEST (strict mode).
///
/// The caller deliberately sets `previous_receipt_hash` to a bogus value on
/// the second receipt before passing it to `append_receipt`. Under strict
/// mode the cipherclerk **rejects** the receipt with
/// `ChainAppendError::ReceiptChainMismatch`; the chain is unchanged.
///
/// Pre-fix the cipherclerk silently rewrote the field, masking forks. This
/// test documents the new fail-closed behavior.
#[test]
fn audit_77_wrong_prev_hash_is_rejected_strict() {
    use pyana_sdk::ChainAppendError;

    let mut cclerk = common::cclerk_from_label("audit-77-strict");
    let cell = cclerk.cell_id("test");

    // Append a valid first receipt.
    let r1 = common::mock_receipt(cell, [1u8; 32], [2u8; 32]);
    cclerk.append_receipt(r1).unwrap();
    let correct_prev = cclerk.receipt_head().unwrap().receipt_hash();

    // Build a second receipt with a deliberately wrong `previous_receipt_hash`.
    let bogus_prev: [u8; 32] = [0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0];
    assert_ne!(bogus_prev, correct_prev, "bogus must differ from correct");

    let r2 = common::mock_receipt_with_prev(cell, [2u8; 32], [3u8; 32], Some(bogus_prev));
    let err = cclerk
        .append_receipt(r2)
        .expect_err("strict mode must reject mismatched prev_hash");
    match err {
        ChainAppendError::ReceiptChainMismatch { expected, got } => {
            assert_eq!(expected, Some(correct_prev), "expected = cclerk head");
            assert_eq!(got, Some(bogus_prev), "got = caller's bogus value");
        }
    }

    // Chain is unchanged on rejection.
    assert_eq!(cclerk.receipt_chain_length(), 1);
    assert_eq!(cclerk.receipt_head().unwrap().receipt_hash(), correct_prev);

    // The (single-element) chain still verifies because we never added a
    // tampered receipt.
    assert!(
        verify_receipt_chain(cclerk.receipt_chain()).is_ok(),
        "untouched chain must still verify"
    );
}

// ---------------------------------------------------------------------------
// 3. Chain verification fails on a tampered chain (post-append)
// ---------------------------------------------------------------------------

/// Build a valid chain of 3, then tamper with the middle receipt's stored
/// `previous_receipt_hash` directly (simulating a malicious ledger read).
/// `verify_receipt_chain` must reject the tampered chain.
#[test]
fn tampered_chain_rejected_by_external_verifier() {
    let mut cclerk = common::cclerk_from_label("tampered-chain");
    let cell = cclerk.cell_id("test");

    for i in 0u8..3 {
        let mut pre = [0u8; 32];
        let mut post = [0u8; 32];
        pre[0] = i;
        post[0] = i + 1;
        let prev = cclerk.receipt_head().map(|r| r.receipt_hash());
        let r = common::mock_receipt_with_prev(cell, pre, post, prev);
        cclerk.append_receipt(r).unwrap();
    }

    // Clone the chain and tamper with the second receipt's prev hash.
    let mut tampered: Vec<_> = cclerk.receipt_chain().to_vec();
    tampered[1].previous_receipt_hash = Some([0xFF; 32]);

    assert!(
        verify_receipt_chain(&tampered).is_err(),
        "verify_receipt_chain must reject a chain with a tampered prev_hash"
    );
}

// ---------------------------------------------------------------------------
// 4. Five-receipt chain — systematic hash-linking check
// ---------------------------------------------------------------------------

/// Five receipts: assert every adjacent pair satisfies
/// `chain[i+1].previous_receipt_hash == Some(chain[i].receipt_hash())`.
#[test]
fn five_receipt_chain_every_link_verified() {
    let mut cclerk = common::cclerk_from_label("five-receipt");
    let cell = cclerk.cell_id("test");

    for i in 0u8..5 {
        let mut pre = [0u8; 32];
        let mut post = [0u8; 32];
        pre[0] = i;
        post[0] = i + 1;
        let prev = cclerk.receipt_head().map(|r| r.receipt_hash());
        let r = common::mock_receipt_with_prev(cell, pre, post, prev);
        cclerk.append_receipt(r).unwrap();
    }

    assert_eq!(cclerk.receipt_chain_length(), 5);

    let chain = cclerk.receipt_chain();
    for i in 1..chain.len() {
        assert_eq!(
            chain[i].previous_receipt_hash,
            Some(chain[i - 1].receipt_hash()),
            "link broken at index {i}"
        );
    }

    assert!(verify_receipt_chain(chain).is_ok());
    assert!(cclerk.verify_own_chain().is_ok());
}
