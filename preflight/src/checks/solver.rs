//! Intent solver checks: ring detection (2-party, 3-party), validation, generalized.

use pyana_intent::CommitmentId;
use pyana_intent::generalized::{
    ExchangeItem, GeneralizedExchange, GeneralizedIntentNode, GeneralizedSolver, can_satisfy,
    item_satisfies,
};
use pyana_intent::solver::{ExchangeSpec, IntentNode, RingSolver, SolverError};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("ring_2party", check_ring_2party),
        run_check("ring_3party", check_ring_3party),
        run_check("validation_rejects", check_validation_rejects),
        run_check("generalized_swap", check_generalized_swap),
    ]
}

fn make_asset_id(name: &str) -> [u8; 32] {
    *blake3::hash(name.as_bytes()).as_bytes()
}

fn make_commitment(label: &str) -> CommitmentId {
    CommitmentId(*blake3::hash(label.as_bytes()).as_bytes())
}

fn make_intent_id(label: &str) -> [u8; 32] {
    *blake3::hash(format!("intent-{label}").as_bytes()).as_bytes()
}

fn check_ring_2party() -> Result<(), String> {
    let solver = RingSolver::new(5);

    let asset_a = make_asset_id("token-A");
    let asset_b = make_asset_id("token-B");

    // Alice has A, wants B. Bob has B, wants A.
    let intents = vec![
        IntentNode {
            intent_id: make_intent_id("alice"),
            exchange: ExchangeSpec {
                offer_asset: asset_a,
                offer_amount: 100,
                want_asset: asset_b,
                want_min_amount: 50,
                min_rate: None,
                max_rate: None,
            },
            creator: make_commitment("alice"),
            expiry: 1000,
        },
        IntentNode {
            intent_id: make_intent_id("bob"),
            exchange: ExchangeSpec {
                offer_asset: asset_b,
                offer_amount: 80,
                want_asset: asset_a,
                want_min_amount: 60,
                min_rate: None,
                max_rate: None,
            },
            creator: make_commitment("bob"),
            expiry: 1000,
        },
    ];

    let graph = solver.build_graph(&intents);
    let rings = solver.find_rings(&graph);

    if rings.is_empty() {
        return Err("should find a 2-party ring trade (A<->B swap)".into());
    }

    // Verify the ring has 2 participants.
    let ring = &rings[0];
    if ring.participants.len() != 2 {
        return Err(format!(
            "2-party ring should have 2 participants, got {}",
            ring.participants.len()
        ));
    }

    // Verify settlements exist.
    if ring.settlements.is_empty() {
        return Err("ring should have settlements".into());
    }

    Ok(())
}

fn check_ring_3party() -> Result<(), String> {
    let solver = RingSolver::new(5);

    let asset_a = make_asset_id("gold");
    let asset_b = make_asset_id("silver");
    let asset_c = make_asset_id("bronze");

    // 3-party cycle: Alice(A->B), Bob(B->C), Carol(C->A)
    let intents = vec![
        IntentNode {
            intent_id: make_intent_id("alice3"),
            exchange: ExchangeSpec {
                offer_asset: asset_a,
                offer_amount: 100,
                want_asset: asset_b,
                want_min_amount: 50,
                min_rate: None,
                max_rate: None,
            },
            creator: make_commitment("alice3"),
            expiry: 2000,
        },
        IntentNode {
            intent_id: make_intent_id("bob3"),
            exchange: ExchangeSpec {
                offer_asset: asset_b,
                offer_amount: 80,
                want_asset: asset_c,
                want_min_amount: 30,
                min_rate: None,
                max_rate: None,
            },
            creator: make_commitment("bob3"),
            expiry: 2000,
        },
        IntentNode {
            intent_id: make_intent_id("carol3"),
            exchange: ExchangeSpec {
                offer_asset: asset_c,
                offer_amount: 60,
                want_asset: asset_a,
                want_min_amount: 40,
                min_rate: None,
                max_rate: None,
            },
            creator: make_commitment("carol3"),
            expiry: 2000,
        },
    ];

    let graph = solver.build_graph(&intents);
    let rings = solver.find_rings(&graph);

    if rings.is_empty() {
        return Err("should find a 3-party ring trade (A->B->C->A)".into());
    }

    // Verify ring has 3 participants.
    let ring = &rings[0];
    if ring.participants.len() != 3 {
        return Err(format!(
            "3-party ring should have 3 participants, got {}",
            ring.participants.len()
        ));
    }

    // Verify 3 settlements.
    if ring.settlements.len() != 3 {
        return Err(format!(
            "3-party ring should have 3 settlements, got {}",
            ring.settlements.len()
        ));
    }

    Ok(())
}

fn check_validation_rejects() -> Result<(), String> {
    let solver = RingSolver::new(5);

    let asset_a = make_asset_id("token-X");
    let asset_b = make_asset_id("token-Y");

    // Incompatible amounts: Alice offers 10, but Bob wants 100.
    let ring = vec![
        IntentNode {
            intent_id: make_intent_id("alice-bad"),
            exchange: ExchangeSpec {
                offer_asset: asset_a,
                offer_amount: 10, // too little
                want_asset: asset_b,
                want_min_amount: 50,
                min_rate: None,
                max_rate: None,
            },
            creator: make_commitment("alice-bad"),
            expiry: 1000,
        },
        IntentNode {
            intent_id: make_intent_id("bob-bad"),
            exchange: ExchangeSpec {
                offer_asset: asset_b,
                offer_amount: 80,
                want_asset: asset_a,
                want_min_amount: 100, // Alice only offers 10!
                min_rate: None,
                max_rate: None,
            },
            creator: make_commitment("bob-bad"),
            expiry: 1000,
        },
    ];

    let result = solver.validate_ring(&ring, 500);
    match result {
        Err(SolverError::InsufficientAmount { .. }) => {} // expected
        Err(other) => return Err(format!("expected InsufficientAmount, got {other}")),
        Ok(_) => return Err("incompatible amounts should be rejected".into()),
    }

    // Too small (single participant).
    let single = vec![IntentNode {
        intent_id: make_intent_id("loner"),
        exchange: ExchangeSpec {
            offer_asset: asset_a,
            offer_amount: 100,
            want_asset: asset_b,
            want_min_amount: 50,
            min_rate: None,
            max_rate: None,
        },
        creator: make_commitment("loner"),
        expiry: 1000,
    }];

    let result = solver.validate_ring(&single, 500);
    match result {
        Err(SolverError::TooSmall) => {} // expected
        Err(other) => return Err(format!("expected TooSmall, got {other}")),
        Ok(_) => return Err("single-participant ring should be rejected".into()),
    }

    Ok(())
}

fn check_generalized_swap() -> Result<(), String> {
    // Test asset-for-capability swap.
    let asset_id = make_asset_id("compute-token");

    // Alice offers 100 tokens, wants read access to "documents/*".
    let alice_offering = vec![ExchangeItem::Asset {
        id: asset_id,
        amount: 100,
    }];
    let alice_wanting = vec![ExchangeItem::Capability {
        actions: vec!["read".into()],
        resource: "documents/*".into(),
        duration_epochs: 10,
    }];

    // Bob offers read+write access to "documents/*", wants tokens.
    let bob_offering = vec![ExchangeItem::Capability {
        actions: vec!["read".into(), "write".into()],
        resource: "documents/*".into(),
        duration_epochs: 20,
    }];
    let bob_wanting = vec![ExchangeItem::Asset {
        id: asset_id,
        amount: 50,
    }];

    // Verify structural compatibility.
    // Bob's offer should satisfy Alice's want (superset of actions, longer duration).
    let bob_satisfies_alice = item_satisfies(&bob_offering[0], &alice_wanting[0]);
    if !bob_satisfies_alice {
        return Err("Bob's capability should satisfy Alice's want".into());
    }

    // Alice's offer should satisfy Bob's want (100 >= 50 tokens).
    let alice_satisfies_bob = item_satisfies(&alice_offering[0], &bob_wanting[0]);
    if !alice_satisfies_bob {
        return Err("Alice's tokens should satisfy Bob's want".into());
    }

    // Build generalized graph and find cycles.
    let nodes = vec![
        GeneralizedIntentNode {
            intent_id: make_intent_id("alice-gen"),
            exchange: GeneralizedExchange {
                offering: alice_offering,
                wanting: alice_wanting,
            },
            creator: make_commitment("alice-gen"),
            expiry: 5000,
            zone: Some("/defi/swap".into()),
        },
        GeneralizedIntentNode {
            intent_id: make_intent_id("bob-gen"),
            exchange: GeneralizedExchange {
                offering: bob_offering,
                wanting: bob_wanting,
            },
            creator: make_commitment("bob-gen"),
            expiry: 5000,
            zone: Some("/services/compute".into()),
        },
    ];

    let solver = GeneralizedSolver::new(5);
    let results = solver.solve(&nodes, 100);

    if results.is_empty() {
        return Err("generalized solver should find the asset-for-capability ring".into());
    }

    // Verify the result has 2 participants.
    if results[0].participants.len() != 2 {
        return Err(format!(
            "expected 2 participants in generalized ring, got {}",
            results[0].participants.len()
        ));
    }

    // Also test can_satisfy at the set level.
    let score = can_satisfy(
        &[ExchangeItem::Asset {
            id: asset_id,
            amount: 100,
        }],
        &[ExchangeItem::Asset {
            id: asset_id,
            amount: 50,
        }],
    );
    match score {
        Some(s) => {
            if s <= 0.0 || s > 1.0 {
                return Err(format!("satisfaction score should be in (0,1], got {s}"));
            }
        }
        None => return Err("100 tokens should satisfy a want of 50".into()),
    }

    Ok(())
}
