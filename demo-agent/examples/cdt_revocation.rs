//! CDT Cascading Revocation Demo
//!
//! Demonstrates cascading revocation through the Capability Derivation Tree (CDT).
//!
//! Scenario: a corporate delegation hierarchy where revoking a mid-level node
//! transitively invalidates ALL downstream capabilities — without enumerating them.
//!
//! Key insights:
//! - Revocation is O(1) to CHECK: walk UP from the cap to its root, checking
//!   each ancestor against the revocation set.
//! - Revocation is O(1) to PERFORM: add a single (cell, slot) to the set.
//! - The CDT + NullifierSet enables VERIFIABLE revocation via membership/non-membership proofs.
//! - New delegation branches after revocation are unaffected.

use std::collections::HashSet;

use pyana_cell::derivation::{DerivationEdge, DerivationNode, DerivationTree, DerivationType};
use pyana_cell::id::CellId;
use pyana_cell::note::Nullifier;
use pyana_cell::nullifier_set::NullifierSet;

/// Create a named CellId from a seed string (deterministic, for demo purposes).
fn named_cell(name: &str) -> CellId {
    let pk = blake3::derive_key("cdt-demo-pk-v1", name.as_bytes());
    let token = blake3::derive_key("cdt-demo-token-v1", name.as_bytes());
    CellId::derive_raw(&pk, &token)
}

/// Shorthand for a turn hash from a seed.
fn turn_hash(seed: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("cdt-demo-turn-v1");
    hasher.update(&seed.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Print a short hex prefix of a CellId.
fn cell_short(cell: &CellId) -> String {
    let b = cell.as_bytes();
    format!("{:02x}{:02x}{:02x}{:02x}", b[0], b[1], b[2], b[3])
}

fn main() {
    println!("=== CDT Cascading Revocation Demo ===\n");

    // =========================================================================
    // STEP 1: Build the delegation hierarchy
    // =========================================================================
    println!("--- Step 1: BUILD DELEGATION HIERARCHY ---\n");
    println!("  Hierarchy:");
    println!("    CEO (root mint)");
    println!("      +-- VP (grant from CEO)");
    println!("            +-- Manager (grant from VP)");
    println!("                  +-- Intern (grant from Manager)");
    println!("                  +-- Database access (introduce: Manager introduces Intern to DB)");
    println!();

    let ceo = named_cell("ceo");
    let vp = named_cell("vp");
    let manager = named_cell("manager");
    let intern = named_cell("intern");
    let database = named_cell("database");

    println!("  CellIds:");
    println!("    CEO:      {}", cell_short(&ceo));
    println!("    VP:       {}", cell_short(&vp));
    println!("    Manager:  {}", cell_short(&manager));
    println!("    Intern:   {}", cell_short(&intern));
    println!("    Database: {}", cell_short(&database));
    println!();

    let mut tree = DerivationTree::new();

    // CEO mints root capability (slot 0).
    tree.record_derivation(DerivationNode {
        cell: ceo,
        slot: 0,
        parent: None,
        created_at: 1000,
        created_by_turn: turn_hash(1),
    });

    // CEO grants to VP (slot 0).
    tree.record_derivation(DerivationNode {
        cell: vp,
        slot: 0,
        parent: Some(DerivationEdge {
            source_cell: ceo,
            source_slot: 0,
            derivation_type: DerivationType::Grant,
        }),
        created_at: 2000,
        created_by_turn: turn_hash(2),
    });

    // VP grants to Manager (slot 0).
    tree.record_derivation(DerivationNode {
        cell: manager,
        slot: 0,
        parent: Some(DerivationEdge {
            source_cell: vp,
            source_slot: 0,
            derivation_type: DerivationType::Grant,
        }),
        created_at: 3000,
        created_by_turn: turn_hash(3),
    });

    // Manager grants to Intern (slot 0).
    tree.record_derivation(DerivationNode {
        cell: intern,
        slot: 0,
        parent: Some(DerivationEdge {
            source_cell: manager,
            source_slot: 0,
            derivation_type: DerivationType::Grant,
        }),
        created_at: 4000,
        created_by_turn: turn_hash(4),
    });

    // Manager introduces Intern to Database (Intern gets DB access at slot 1).
    tree.record_derivation(DerivationNode {
        cell: intern,
        slot: 1,
        parent: Some(DerivationEdge {
            source_cell: manager,
            source_slot: 0,
            derivation_type: DerivationType::Introduce,
        }),
        created_at: 4500,
        created_by_turn: turn_hash(5),
    });

    println!(
        "  CDT now has {} nodes, {} root(s)",
        tree.len(),
        tree.roots().len()
    );

    // Show the derivation path for intern's DB access.
    let intern_db_path = tree.derivation_path(&intern, 1);
    println!(
        "  Intern's DB access path (slot 1): {} hops to root",
        intern_db_path.len() - 1
    );
    for (i, node) in intern_db_path.iter().enumerate() {
        let label = match node.cell {
            c if c == intern => "Intern",
            c if c == manager => "Manager",
            c if c == vp => "VP",
            c if c == ceo => "CEO",
            _ => "?",
        };
        println!(
            "    [{}] {} (slot {}){}",
            i,
            label,
            node.slot,
            if node.parent.is_none() {
                " <- ROOT MINT"
            } else {
                ""
            }
        );
    }
    println!();

    // =========================================================================
    // STEP 2: Normal operation — Intern can access Database
    // =========================================================================
    println!("--- Step 2: NORMAL OPERATION ---\n");

    let revocation_set: HashSet<(CellId, u32)> = HashSet::new();

    let intern_valid = !tree.has_revoked_ancestor(&intern, 1, &revocation_set);
    println!(
        "  Intern DB access (slot 1): {}",
        if intern_valid { "VALID" } else { "REVOKED" }
    );
    assert!(intern_valid);

    let intern_cap_valid = !tree.has_revoked_ancestor(&intern, 0, &revocation_set);
    println!(
        "  Intern base cap (slot 0): {}",
        if intern_cap_valid {
            "VALID"
        } else {
            "REVOKED"
        }
    );
    assert!(intern_cap_valid);
    println!();

    // =========================================================================
    // STEP 3: VP is compromised — REVOKE VP's capability
    // =========================================================================
    println!("--- Step 3: VP COMPROMISED -- REVOKE VP ---\n");
    println!("  Adding VP (cell={}, slot=0) to revocation set...", cell_short(&vp));

    let mut revocation_set: HashSet<(CellId, u32)> = HashSet::new();
    revocation_set.insert((vp, 0));
    println!("  Revocation set size: {}", revocation_set.len());
    println!();

    // Check cascading effects.
    println!("  Cascading revocation checks:");
    println!();

    let vp_revoked = tree.has_revoked_ancestor(&vp, 0, &revocation_set);
    println!(
        "    has_revoked_ancestor(VP, 0)      = {} (VP itself is revoked)",
        vp_revoked
    );
    assert!(vp_revoked);

    let mgr_revoked = tree.has_revoked_ancestor(&manager, 0, &revocation_set);
    println!(
        "    has_revoked_ancestor(Manager, 0) = {} (Manager derived from VP)",
        mgr_revoked
    );
    assert!(mgr_revoked);

    let intern_revoked = tree.has_revoked_ancestor(&intern, 0, &revocation_set);
    println!(
        "    has_revoked_ancestor(Intern, 0)  = {} (Intern derived from Manager derived from VP)",
        intern_revoked
    );
    assert!(intern_revoked);

    let intern_db_revoked = tree.has_revoked_ancestor(&intern, 1, &revocation_set);
    println!(
        "    has_revoked_ancestor(Intern, 1)  = {} (DB access derived from Manager derived from VP)",
        intern_db_revoked
    );
    assert!(intern_db_revoked);

    let ceo_revoked = tree.has_revoked_ancestor(&ceo, 0, &revocation_set);
    println!(
        "    has_revoked_ancestor(CEO, 0)     = {} (CEO is UPSTREAM, not downstream)",
        ceo_revoked
    );
    assert!(!ceo_revoked);
    println!();

    // =========================================================================
    // STEP 4: Show — revocation check is O(1) per ancestor hop
    // =========================================================================
    println!("--- Step 4: O(1) REVOCATION CHECK ---\n");

    println!("  `has_revoked_ancestor()` walks UP the tree (child -> parent -> grandparent)");
    println!("  checking each node against the revocation HashSet (O(1) lookup per node).");
    println!();
    println!("  For Intern's DB access (slot 1), the walk is:");
    println!("    Intern(slot=1) -> check revocation_set: NO");
    println!("    Manager(slot=0) -> check revocation_set: NO");
    println!("    VP(slot=0)      -> check revocation_set: YES -> REVOKED");
    println!();
    println!("  Total work: 3 hash lookups. Much cheaper than walking DOWN from VP");
    println!("  to enumerate all descendants (which could be unbounded).");
    println!();
    println!("  Contrast with flat revocation:");
    println!("    Without CDT: must enumerate and individually revoke VP, Manager, Intern,");
    println!("    Intern's DB cap, and any future delegates. O(n) insertions.");
    println!("    With CDT: revoke VP once (1 insertion), all descendants are transitively invalid.");
    println!();

    // =========================================================================
    // STEP 5: VERIFIABLE revocation via NullifierSet
    // =========================================================================
    println!("--- Step 5: VERIFIABLE REVOCATION (NullifierSet) ---\n");

    // Compute the revocation hash for VP's capability.
    let vp_revocation_hash = DerivationTree::revocation_hash(&vp, 0);
    println!(
        "  VP revocation_hash: {:02x}{:02x}{:02x}{:02x}...",
        vp_revocation_hash[0], vp_revocation_hash[1], vp_revocation_hash[2], vp_revocation_hash[3]
    );

    // Insert into a NullifierSet (the verifiable revocation registry).
    let mut nullifier_set = NullifierSet::new();
    let vp_nullifier = Nullifier(vp_revocation_hash);
    nullifier_set
        .insert(vp_nullifier)
        .expect("first insert should succeed");

    let root = nullifier_set.root();
    println!(
        "  NullifierSet root: {:02x}{:02x}{:02x}{:02x}...",
        root[0], root[1], root[2], root[3]
    );
    println!();

    // Any verifier can now check: "is VP's cap in the revocation set?"
    let vp_is_revoked = nullifier_set.contains(&vp_nullifier);
    println!("  VP membership check: {} (revoked)", vp_is_revoked);
    assert!(vp_is_revoked);

    // CEO's cap is NOT revoked — generate a non-membership proof.
    let ceo_revocation_hash = DerivationTree::revocation_hash(&ceo, 0);
    let ceo_nullifier = Nullifier(ceo_revocation_hash);
    let ceo_non_membership = nullifier_set.prove_non_membership(&ceo_nullifier);
    assert!(ceo_non_membership.is_some());
    let ceo_proof = ceo_non_membership.unwrap();
    let ceo_valid = NullifierSet::verify_non_membership(&ceo_proof, &root);
    println!(
        "  CEO non-membership proof: verification = {} (still valid)",
        if ceo_valid { "PASS" } else { "FAIL" }
    );
    assert!(ceo_valid);

    // VP's cap IS revoked — non-membership proof should fail (returns None).
    let vp_non_membership = nullifier_set.prove_non_membership(&vp_nullifier);
    println!(
        "  VP non-membership proof: {} (correctly indicates revocation)",
        if vp_non_membership.is_none() {
            "CANNOT GENERATE"
        } else {
            "ERROR: should not exist"
        }
    );
    assert!(vp_non_membership.is_none());
    println!();

    println!("  Verification summary:");
    println!("    - Any verifier with the NullifierSet root can check revocation status.");
    println!("    - Membership proof (VP) -> cap is revoked.");
    println!("    - Non-membership proof (CEO) -> cap is still valid.");
    println!("    - To check a derived cap: walk UP ancestors, check each against the set.");
    println!();

    // =========================================================================
    // STEP 6: New delegation AFTER revocation
    // =========================================================================
    println!("--- Step 6: NEW DELEGATION AFTER REVOCATION ---\n");

    let new_vp = named_cell("new-vp");
    let manager2 = named_cell("manager2");

    println!("  CEO grants to NewVP (replacement for compromised VP)...");
    tree.record_derivation(DerivationNode {
        cell: new_vp,
        slot: 0,
        parent: Some(DerivationEdge {
            source_cell: ceo,
            source_slot: 0,
            derivation_type: DerivationType::Grant,
        }),
        created_at: 6000,
        created_by_turn: turn_hash(6),
    });

    println!("  NewVP grants to Manager2...");
    tree.record_derivation(DerivationNode {
        cell: manager2,
        slot: 0,
        parent: Some(DerivationEdge {
            source_cell: new_vp,
            source_slot: 0,
            derivation_type: DerivationType::Grant,
        }),
        created_at: 7000,
        created_by_turn: turn_hash(7),
    });

    println!();
    println!(
        "  CDT now has {} nodes (original 5 + 2 new)",
        tree.len()
    );
    println!();

    // Check: new branch is NOT affected by the VP revocation.
    let new_vp_revoked = tree.has_revoked_ancestor(&new_vp, 0, &revocation_set);
    println!(
        "  has_revoked_ancestor(NewVP, 0)     = {} (new branch, not under VP)",
        new_vp_revoked
    );
    assert!(!new_vp_revoked);

    let manager2_revoked = tree.has_revoked_ancestor(&manager2, 0, &revocation_set);
    println!(
        "  has_revoked_ancestor(Manager2, 0)  = {} (derived from NewVP, not VP)",
        manager2_revoked
    );
    assert!(!manager2_revoked);

    // But the OLD branch is still revoked.
    let old_intern_still_revoked = tree.has_revoked_ancestor(&intern, 0, &revocation_set);
    println!(
        "  has_revoked_ancestor(Intern, 0)    = {} (old branch, still under revoked VP)",
        old_intern_still_revoked
    );
    assert!(old_intern_still_revoked);
    println!();

    // Verify the new caps via NullifierSet too.
    let new_vp_revocation_hash = DerivationTree::revocation_hash(&new_vp, 0);
    let new_vp_nullifier = Nullifier(new_vp_revocation_hash);
    let new_vp_proof = nullifier_set.prove_non_membership(&new_vp_nullifier);
    assert!(new_vp_proof.is_some());
    let new_vp_valid = NullifierSet::verify_non_membership(&new_vp_proof.unwrap(), &root);
    println!(
        "  NewVP NullifierSet non-membership: {} (not revoked)",
        if new_vp_valid { "PASS" } else { "FAIL" }
    );
    assert!(new_vp_valid);
    println!();

    // =========================================================================
    // STEP 7: Compare with flat revocation
    // =========================================================================
    println!("--- Step 7: CDT vs FLAT REVOCATION COMPARISON ---\n");

    // Flat revocation: must enumerate all descendants and revoke each one.
    let descendants_of_vp = tree.descendants(&vp, 0);
    println!(
        "  Descendants of VP (that WOULD need individual revocation in flat model): {}",
        descendants_of_vp.len()
    );
    for desc in &descendants_of_vp {
        let label = match desc.cell {
            c if c == manager => "Manager",
            c if c == intern => "Intern",
            _ => "?",
        };
        println!("    - {} (slot {})", label, desc.slot);
    }
    println!();

    println!("  Flat revocation cost:");
    println!(
        "    Revocations needed: {} (VP + {} descendants)",
        1 + descendants_of_vp.len(),
        descendants_of_vp.len()
    );
    println!(
        "    NullifierSet insertions: {}",
        1 + descendants_of_vp.len()
    );
    println!();
    println!("  CDT revocation cost:");
    println!("    Revocations needed: 1 (VP only)");
    println!("    NullifierSet insertions: 1");
    println!("    Verification cost: O(depth) ancestor walk per check");
    println!();
    println!("  In a real hierarchy with thousands of delegates under VP,");
    println!("  the CDT approach is O(1) to revoke vs O(n) for flat enumeration.");
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================
    println!("--- SUMMARY ---\n");
    println!("  The Capability Derivation Tree (CDT) enables:");
    println!("    1. CASCADING REVOCATION: revoke one node, all descendants are invalid.");
    println!("    2. O(1) REVOCATION: single insertion into revocation set.");
    println!("    3. O(depth) VERIFICATION: walk ancestor chain, check each against set.");
    println!("    4. VERIFIABLE PROOFS: NullifierSet membership/non-membership proofs.");
    println!("    5. ISOLATION: new delegation branches after revocation are unaffected.");
    println!("    6. NO ENUMERATION: revoker doesn't need to know all descendants.");
    println!();
    println!("=== CDT Cascading Revocation Demo Complete ===");
}
