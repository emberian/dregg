//! Stage 7-γ.2 Phase 1 — bilateral cross-cell algebraic binding.
//!
//! See `STAGE-7-GAMMA-2-PI-DESIGN.md` for the full spec.
//!
//! This module owns:
//!   * Canonical id derivation for the three bilateral effects
//!     (`transfer_id`, `grant_id`, `intro_id`) — §3.
//!   * `ExpectedBilateral` schedule reconstruction from `(call_forest, ACTOR_NONCE)`
//!     — §4.2.
//!   * Per-cell accumulator-root recomputation that the verifier compares
//!     against PI[OUTGOING_TRANSFER_ROOT_BASE..] etc. — §4.3-4.4.
//!
//! The accumulator absorb order is **trace-row-index order in the cell's
//! per-cell projection** — DFS over the call_forest, taking each effect
//! whose role on `cell_id` is one of (sender, recipient, introducer,
//! recipient-of-intro, target-of-intro). This must mirror exactly what
//! `turn::executor::convert_turn_effects_to_vm` walks, otherwise the AIR
//! (when γ.2.1 lands) and the verifier will disagree on the root.
//!
//! ## ID derivation summary
//!
//! Every bilateral id is the 4-felt Poseidon2 of a canonical preimage:
//!
//! - `transfer_id = Poseidon2("pyana-transfer-id-v1" || from || to || amount_be || nonce_be)`
//! - `grant_id    = Poseidon2("pyana-grant-id-v1"    || from || to || cap_hash || nonce_be)`
//! - `intro_id    = Poseidon2("pyana-intro-id-v1"    || introducer || recipient || target ||
//!                             permissions_bits || nonce_be)`
//!
//! ## Accumulator update
//!
//! For one bilateral entry, the per-direction accumulator state advances:
//!
//! ```text
//! acc' = absorb_4(acc, [id[0], id[1], id[2], id[3]])
//! acc'' = absorb_4(acc', [peer[0], peer[1], peer[2], peer[3]])
//! ```
//!
//! where `peer` is the peer cell-id projected via `canonical_32_to_felts_4`.
//! Two absorbs per entry: one for the id, one for the peer-cell encoding.
//! This is the form the future AIR will materialize as aux columns. The
//! starting state is `[BabyBear::ZERO; 4]` (sentinel-equivalent).

use crate::action::Effect;
use crate::forest::CallTree;
use crate::turn::Turn;
use pyana_cell::AuthRequired;
use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2::hash_4_to_1;
use pyana_commit::typed::canonical_32_to_felts_4;
use pyana_types::CellId;

// ---------------------------------------------------------------------------
// Domain separators
// ---------------------------------------------------------------------------

const TRANSFER_DOMAIN: &[u8] = b"pyana-transfer-id-v1";
const GRANT_DOMAIN: &[u8] = b"pyana-grant-id-v1";
const INTRO_DOMAIN: &[u8] = b"pyana-intro-id-v1";

// Distinct accumulator-update salts per kind/direction. Each ensures that
// (e.g.) an outbound transfer accumulator cannot be confused with an inbound
// one even if the ids accidentally collided across directions. Single felts
// folded into the accumulator state-update.
const OUTBOUND_TRANSFER_SALT: u32 = 0x4F54_5832; // "OTX2"
const INBOUND_TRANSFER_SALT: u32 = 0x4954_5832; // "ITX2"
const OUTBOUND_GRANT_SALT: u32 = 0x4F47_5232; // "OGR2"
const INBOUND_GRANT_SALT: u32 = 0x4947_5232; // "IGR2"
const INTRO_INTRODUCER_SALT: u32 = 0x4949_4E32; // "IIN2"
const INTRO_RECIPIENT_SALT: u32 = 0x4952_4332; // "IRC2"
const INTRO_TARGET_SALT: u32 = 0x4954_4732; // "ITG2"

// ---------------------------------------------------------------------------
// Roles
// ---------------------------------------------------------------------------

/// Direction of a Transfer or Grant from this cell's perspective.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TransferDirection {
    Outbound,
    Inbound,
}

/// Role of this cell in an Introduce effect.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum IntroduceRole {
    Introducer,
    Recipient,
    Target,
}

// ---------------------------------------------------------------------------
// Canonical id derivation
// ---------------------------------------------------------------------------

/// Project a 4-felt id through the Poseidon2 absorb chain. The output is a
/// 4-felt commitment with ~124-bit collision resistance.
fn poseidon2_id_from_bytes(domain: &[u8], payload: &[u8]) -> [BabyBear; 4] {
    // Compose the canonical preimage: domain || payload.
    // We hash with BLAKE3 first to get a stable 32-byte commitment to the
    // preimage, then project into 4 BabyBear felts via canonical_32_to_felts_4.
    // This matches the existing 4-felt commitment scheme used for TURN_HASH,
    // PREVIOUS_RECEIPT_HASH, etc. (`compute_turn_identity_pi`).
    let mut hasher = blake3::Hasher::new();
    hasher.update(domain);
    hasher.update(payload);
    let h: [u8; 32] = *hasher.finalize().as_bytes();
    canonical_32_to_felts_4(&h)
}

/// Compute `transfer_id` from canonical surface data.
///
/// `transfer_id = Poseidon2( "pyana-transfer-id-v1" || from || to || amount_be || nonce_be )`
///
/// This matches §3.1 of `STAGE-7-GAMMA-2-PI-DESIGN.md`.
pub fn derive_transfer_id(
    from: &CellId,
    to: &CellId,
    amount: u64,
    actor_nonce: u64,
) -> [BabyBear; 4] {
    let mut payload = Vec::with_capacity(80);
    payload.extend_from_slice(from.as_bytes());
    payload.extend_from_slice(to.as_bytes());
    payload.extend_from_slice(&amount.to_be_bytes());
    payload.extend_from_slice(&actor_nonce.to_be_bytes());
    poseidon2_id_from_bytes(TRANSFER_DOMAIN, &payload)
}

/// Compute `cap_entry_hash` from a `CapabilityRef`.
///
/// Projects (target, slot, permissions_bits, expiry, breadstuff?) into a
/// stable 32-byte commitment. Used as a component of `grant_id`.
pub fn compute_cap_entry_hash(cap: &pyana_cell::CapabilityRef) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-cap-entry-v1");
    hasher.update(cap.target.as_bytes());
    hasher.update(&cap.slot.to_le_bytes());
    hasher.update(&[permissions_to_bits(&cap.permissions) as u8]);
    if let Some(exp) = cap.expires_at {
        hasher.update(&[1u8]);
        hasher.update(&exp.to_le_bytes());
    } else {
        hasher.update(&[0u8]);
    }
    if let Some(b) = &cap.breadstuff {
        hasher.update(&[1u8]);
        hasher.update(b);
    } else {
        hasher.update(&[0u8]);
    }
    *hasher.finalize().as_bytes()
}

/// Compute `grant_id` from canonical surface data.
///
/// `grant_id = Poseidon2( "pyana-grant-id-v1" || grantor || grantee || cap_entry_hash || nonce_be )`
pub fn derive_grant_id(
    grantor: &CellId,
    grantee: &CellId,
    cap_entry_hash: &[u8; 32],
    actor_nonce: u64,
) -> [BabyBear; 4] {
    let mut payload = Vec::with_capacity(104);
    payload.extend_from_slice(grantor.as_bytes());
    payload.extend_from_slice(grantee.as_bytes());
    payload.extend_from_slice(cap_entry_hash);
    payload.extend_from_slice(&actor_nonce.to_be_bytes());
    poseidon2_id_from_bytes(GRANT_DOMAIN, &payload)
}

/// Encode `AuthRequired` into a stable 4-byte bit mask. Distinct values for
/// distinct semantic content; the bit layout is part of the binding so the
/// AIR (γ.2.1) can route on it.
pub fn permissions_to_bits(p: &AuthRequired) -> u32 {
    match p {
        AuthRequired::None => 0x0000_0001,
        AuthRequired::Signature => 0x0000_0002,
        AuthRequired::Proof => 0x0000_0004,
        AuthRequired::Either => 0x0000_0008,
        AuthRequired::Impossible => 0x0000_0010,
    }
}

/// Compute `intro_id` from canonical surface data.
///
/// `intro_id = Poseidon2( "pyana-intro-id-v1" || introducer || recipient || target ||
///                        permissions_bits || nonce_be )`
pub fn derive_intro_id(
    introducer: &CellId,
    recipient: &CellId,
    target: &CellId,
    permissions: &AuthRequired,
    actor_nonce: u64,
) -> [BabyBear; 4] {
    let mut payload = Vec::with_capacity(108);
    payload.extend_from_slice(introducer.as_bytes());
    payload.extend_from_slice(recipient.as_bytes());
    payload.extend_from_slice(target.as_bytes());
    payload.extend_from_slice(&permissions_to_bits(permissions).to_be_bytes());
    payload.extend_from_slice(&actor_nonce.to_be_bytes());
    poseidon2_id_from_bytes(INTRO_DOMAIN, &payload)
}

// ---------------------------------------------------------------------------
// Accumulator
// ---------------------------------------------------------------------------

/// Absorb one 4-felt block into a 4-felt accumulator state. Component-wise
/// pairing pattern (same shape as `pyana_commit::typed::absorb_4`).
fn absorb_4(chain: [BabyBear; 4], block: [BabyBear; 4]) -> [BabyBear; 4] {
    [
        hash_4_to_1(&[chain[0], block[0], chain[1], block[1]]),
        hash_4_to_1(&[chain[1], block[1], chain[2], block[2]]),
        hash_4_to_1(&[chain[2], block[2], chain[3], block[3]]),
        hash_4_to_1(&[chain[3], block[3], chain[0], block[0]]),
    ]
}

/// Fold one bilateral entry into a running accumulator.
///
/// Each entry contributes three absorbs: a domain salt (so outbound and
/// inbound accumulators differ even at zero entries — wait, sentinels
/// stay all-zero because we only absorb when *adding* — so the salt only
/// runs once per non-empty entry), the id, and the peer cell-id encoding.
fn fold_entry(
    acc: [BabyBear; 4],
    salt: u32,
    id: [BabyBear; 4],
    peer: [BabyBear; 4],
) -> [BabyBear; 4] {
    let salt_block = [
        BabyBear::new(salt & 0x7FFF_FFFF),
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ];
    let acc = absorb_4(acc, salt_block);
    let acc = absorb_4(acc, id);
    absorb_4(acc, peer)
}

// ---------------------------------------------------------------------------
// Schedule
// ---------------------------------------------------------------------------

/// One bilateral Transfer in the turn's schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransferEntry {
    pub from: CellId,
    pub to: CellId,
    pub amount: u64,
}

impl TransferEntry {
    pub fn id(&self, actor_nonce: u64) -> [BabyBear; 4] {
        derive_transfer_id(&self.from, &self.to, self.amount, actor_nonce)
    }
}

/// One bilateral GrantCapability.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrantEntry {
    pub from: CellId,
    pub to: CellId,
    pub cap_entry_hash: [u8; 32],
}

impl GrantEntry {
    pub fn id(&self, actor_nonce: u64) -> [BabyBear; 4] {
        derive_grant_id(&self.from, &self.to, &self.cap_entry_hash, actor_nonce)
    }
}

/// One trilateral Introduce.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntroduceEntry {
    pub introducer: CellId,
    pub recipient: CellId,
    pub target: CellId,
    pub permissions: AuthRequired,
}

impl IntroduceEntry {
    pub fn id(&self, actor_nonce: u64) -> [BabyBear; 4] {
        derive_intro_id(
            &self.introducer,
            &self.recipient,
            &self.target,
            &self.permissions,
            actor_nonce,
        )
    }
}

/// The expected bilateral schedule for a turn: every Transfer / Grant /
/// Introduce in DFS-call_forest order. The verifier computes this from
/// `(call_forest, ACTOR_NONCE)` alone; no per-cell PI / witness is needed.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ExpectedBilateral {
    pub transfers: Vec<TransferEntry>,
    pub grants: Vec<GrantEntry>,
    pub introduces: Vec<IntroduceEntry>,
}

impl ExpectedBilateral {
    /// Walk the call_forest DFS and collect every bilateral effect in
    /// trace-row-index order. This **must** mirror the per-cell projection
    /// in `convert_turn_effects_to_vm` so that per-cell accumulator order
    /// matches when filtered by role.
    pub fn from_turn(turn: &Turn) -> Self {
        fn walk(tree: &CallTree, sched: &mut ExpectedBilateral) {
            for effect in &tree.action.effects {
                match effect {
                    Effect::Transfer { from, to, amount } => {
                        sched.transfers.push(TransferEntry {
                            from: from.clone(),
                            to: to.clone(),
                            amount: *amount,
                        });
                    }
                    Effect::GrantCapability { from, to, cap } => {
                        sched.grants.push(GrantEntry {
                            from: from.clone(),
                            to: to.clone(),
                            cap_entry_hash: compute_cap_entry_hash(cap),
                        });
                    }
                    Effect::Introduce {
                        introducer,
                        recipient,
                        target,
                        permissions,
                    } => {
                        sched.introduces.push(IntroduceEntry {
                            introducer: introducer.clone(),
                            recipient: recipient.clone(),
                            target: target.clone(),
                            permissions: permissions.clone(),
                        });
                    }
                    _ => {}
                }
            }
            for child in &tree.children {
                walk(child, sched);
            }
        }
        let mut sched = ExpectedBilateral::default();
        for root in &turn.call_forest.roots {
            walk(root, &mut sched);
        }
        sched
    }

    /// Counts of bilateral effects on the given cell, per the seven PI
    /// count slots. Returns the same shape the verifier checks against
    /// PI[OUTBOUND_TRANSFER_COUNT..INTRO_AS_TARGET_COUNT].
    pub fn counts_for(&self, cell: &CellId) -> BilateralCounts {
        let mut c = BilateralCounts::default();
        for t in &self.transfers {
            if &t.from == cell {
                c.outbound_transfer += 1;
            }
            if &t.to == cell {
                c.inbound_transfer += 1;
            }
        }
        for g in &self.grants {
            if &g.from == cell {
                c.outbound_grant += 1;
            }
            if &g.to == cell {
                c.inbound_grant += 1;
            }
        }
        for i in &self.introduces {
            if &i.introducer == cell {
                c.intro_as_introducer += 1;
            }
            if &i.recipient == cell {
                c.intro_as_recipient += 1;
            }
            if &i.target == cell {
                c.intro_as_target += 1;
            }
        }
        c
    }

    /// Recompute the seven 4-felt accumulator roots for a given cell. Each
    /// root absorbs the bilateral entries in trace-row order, restricted to
    /// the rows in which `cell` plays the corresponding role. Sentinel:
    /// `[BabyBear::ZERO; 4]` when no entries of that role exist.
    pub fn roots_for(&self, cell: &CellId, actor_nonce: u64) -> BilateralRoots {
        let mut roots = BilateralRoots::default();
        // Transfers in DFS order; route to outbound/inbound by direction.
        for t in &self.transfers {
            let id = t.id(actor_nonce);
            if &t.from == cell {
                let peer = canonical_32_to_felts_4(t.to.as_bytes());
                roots.outgoing_transfer =
                    fold_entry(roots.outgoing_transfer, OUTBOUND_TRANSFER_SALT, id, peer);
            }
            if &t.to == cell {
                let peer = canonical_32_to_felts_4(t.from.as_bytes());
                roots.incoming_transfer =
                    fold_entry(roots.incoming_transfer, INBOUND_TRANSFER_SALT, id, peer);
            }
        }
        for g in &self.grants {
            let id = g.id(actor_nonce);
            if &g.from == cell {
                let peer = canonical_32_to_felts_4(g.to.as_bytes());
                roots.outgoing_grant =
                    fold_entry(roots.outgoing_grant, OUTBOUND_GRANT_SALT, id, peer);
            }
            if &g.to == cell {
                let peer = canonical_32_to_felts_4(g.from.as_bytes());
                roots.incoming_grant =
                    fold_entry(roots.incoming_grant, INBOUND_GRANT_SALT, id, peer);
            }
        }
        for intro in &self.introduces {
            let id = intro.id(actor_nonce);
            // Three roles per intro entry; each role's accumulator gets
            // (id, peer) where peer = recipient/target packing. We use the
            // "other" cell as peer per role: introducer's peer = recipient,
            // recipient's peer = introducer, target's peer = introducer.
            if &intro.introducer == cell {
                let peer = canonical_32_to_felts_4(intro.recipient.as_bytes());
                roots.intro_as_introducer =
                    fold_entry(roots.intro_as_introducer, INTRO_INTRODUCER_SALT, id, peer);
            }
            if &intro.recipient == cell {
                let peer = canonical_32_to_felts_4(intro.introducer.as_bytes());
                roots.intro_as_recipient =
                    fold_entry(roots.intro_as_recipient, INTRO_RECIPIENT_SALT, id, peer);
            }
            if &intro.target == cell {
                let peer = canonical_32_to_felts_4(intro.introducer.as_bytes());
                roots.intro_as_target =
                    fold_entry(roots.intro_as_target, INTRO_TARGET_SALT, id, peer);
            }
        }
        roots
    }
}

/// Per-cell counts of bilateral effects, mirroring the seven PI count slots.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BilateralCounts {
    pub outbound_transfer: u32,
    pub inbound_transfer: u32,
    pub outbound_grant: u32,
    pub inbound_grant: u32,
    pub intro_as_introducer: u32,
    pub intro_as_recipient: u32,
    pub intro_as_target: u32,
}

/// Per-cell 4-felt accumulator roots, mirroring the seven PI root fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BilateralRoots {
    pub outgoing_transfer: [BabyBear; 4],
    pub incoming_transfer: [BabyBear; 4],
    pub outgoing_grant: [BabyBear; 4],
    pub incoming_grant: [BabyBear; 4],
    pub intro_as_introducer: [BabyBear; 4],
    pub intro_as_recipient: [BabyBear; 4],
    pub intro_as_target: [BabyBear; 4],
}

impl Default for BilateralRoots {
    fn default() -> Self {
        Self {
            outgoing_transfer: [BabyBear::ZERO; 4],
            incoming_transfer: [BabyBear::ZERO; 4],
            outgoing_grant: [BabyBear::ZERO; 4],
            incoming_grant: [BabyBear::ZERO; 4],
            intro_as_introducer: [BabyBear::ZERO; 4],
            intro_as_recipient: [BabyBear::ZERO; 4],
            intro_as_target: [BabyBear::ZERO; 4],
        }
    }
}

// ---------------------------------------------------------------------------
// PI projection / extraction helpers
// ---------------------------------------------------------------------------

/// Project this cell's bilateral counts + roots into the γ.2 slots of a PI
/// vector. The vector must be at least `pi::BASE_COUNT` long; the function
/// writes slots 38..73 (counts + roots) and leaves IS_AGENT_CELL untouched
/// (the executor decides that separately).
pub fn project_into_pi(pi: &mut [BabyBear], counts: &BilateralCounts, roots: &BilateralRoots) {
    use pyana_circuit::effect_vm::pi as p;

    pi[p::OUTBOUND_TRANSFER_COUNT] = BabyBear::new(counts.outbound_transfer);
    pi[p::INBOUND_TRANSFER_COUNT] = BabyBear::new(counts.inbound_transfer);
    pi[p::OUTBOUND_GRANT_COUNT] = BabyBear::new(counts.outbound_grant);
    pi[p::INBOUND_GRANT_COUNT] = BabyBear::new(counts.inbound_grant);
    pi[p::INTRO_AS_INTRODUCER_COUNT] = BabyBear::new(counts.intro_as_introducer);
    pi[p::INTRO_AS_RECIPIENT_COUNT] = BabyBear::new(counts.intro_as_recipient);
    pi[p::INTRO_AS_TARGET_COUNT] = BabyBear::new(counts.intro_as_target);

    for i in 0..4 {
        pi[p::OUTGOING_TRANSFER_ROOT_BASE + i] = roots.outgoing_transfer[i];
        pi[p::INCOMING_TRANSFER_ROOT_BASE + i] = roots.incoming_transfer[i];
        pi[p::OUTGOING_GRANT_ROOT_BASE + i] = roots.outgoing_grant[i];
        pi[p::INCOMING_GRANT_ROOT_BASE + i] = roots.incoming_grant[i];
        pi[p::INTRO_AS_INTRODUCER_ROOT_BASE + i] = roots.intro_as_introducer[i];
        pi[p::INTRO_AS_RECIPIENT_ROOT_BASE + i] = roots.intro_as_recipient[i];
        pi[p::INTRO_AS_TARGET_ROOT_BASE + i] = roots.intro_as_target[i];
    }
}

/// Extract the γ.2 bilateral counts + roots from a PI vector.
pub fn extract_from_pi(pi: &[BabyBear]) -> (BilateralCounts, BilateralRoots) {
    use pyana_circuit::effect_vm::pi as p;
    let counts = BilateralCounts {
        outbound_transfer: pi[p::OUTBOUND_TRANSFER_COUNT].as_u32(),
        inbound_transfer: pi[p::INBOUND_TRANSFER_COUNT].as_u32(),
        outbound_grant: pi[p::OUTBOUND_GRANT_COUNT].as_u32(),
        inbound_grant: pi[p::INBOUND_GRANT_COUNT].as_u32(),
        intro_as_introducer: pi[p::INTRO_AS_INTRODUCER_COUNT].as_u32(),
        intro_as_recipient: pi[p::INTRO_AS_RECIPIENT_COUNT].as_u32(),
        intro_as_target: pi[p::INTRO_AS_TARGET_COUNT].as_u32(),
    };
    let read4 =
        |base: usize| -> [BabyBear; 4] { [pi[base], pi[base + 1], pi[base + 2], pi[base + 3]] };
    let roots = BilateralRoots {
        outgoing_transfer: read4(p::OUTGOING_TRANSFER_ROOT_BASE),
        incoming_transfer: read4(p::INCOMING_TRANSFER_ROOT_BASE),
        outgoing_grant: read4(p::OUTGOING_GRANT_ROOT_BASE),
        incoming_grant: read4(p::INCOMING_GRANT_ROOT_BASE),
        intro_as_introducer: read4(p::INTRO_AS_INTRODUCER_ROOT_BASE),
        intro_as_recipient: read4(p::INTRO_AS_RECIPIENT_ROOT_BASE),
        intro_as_target: read4(p::INTRO_AS_TARGET_ROOT_BASE),
    };
    (counts, roots)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn transfer_id_is_deterministic_and_distinct_per_nonce() {
        let id1 = derive_transfer_id(&cid(1), &cid(2), 100, 7);
        let id2 = derive_transfer_id(&cid(1), &cid(2), 100, 7);
        assert_eq!(id1, id2);
        let id3 = derive_transfer_id(&cid(1), &cid(2), 100, 8);
        assert_ne!(id1, id3);
    }

    #[test]
    fn transfer_id_differs_with_swapped_endpoints() {
        let id1 = derive_transfer_id(&cid(1), &cid(2), 100, 7);
        let id2 = derive_transfer_id(&cid(2), &cid(1), 100, 7);
        assert_ne!(id1, id2);
    }

    #[test]
    fn transfer_id_differs_with_amount() {
        let id1 = derive_transfer_id(&cid(1), &cid(2), 100, 7);
        let id2 = derive_transfer_id(&cid(1), &cid(2), 101, 7);
        assert_ne!(id1, id2);
    }

    #[test]
    fn grant_id_is_deterministic_and_distinct() {
        let h = [0xAB; 32];
        let id1 = derive_grant_id(&cid(1), &cid(2), &h, 7);
        let id2 = derive_grant_id(&cid(1), &cid(2), &h, 7);
        assert_eq!(id1, id2);
        let h2 = [0xCD; 32];
        let id3 = derive_grant_id(&cid(1), &cid(2), &h2, 7);
        assert_ne!(id1, id3);
    }

    #[test]
    fn intro_id_distinct_per_permission_byte() {
        let id_none = derive_intro_id(&cid(1), &cid(2), &cid(3), &AuthRequired::None, 7);
        let id_sig = derive_intro_id(&cid(1), &cid(2), &cid(3), &AuthRequired::Signature, 7);
        let id_proof = derive_intro_id(&cid(1), &cid(2), &cid(3), &AuthRequired::Proof, 7);
        assert_ne!(id_none, id_sig);
        assert_ne!(id_sig, id_proof);
        assert_ne!(id_none, id_proof);
    }

    #[test]
    fn permissions_bits_distinct() {
        let bs: Vec<u32> = [
            AuthRequired::None,
            AuthRequired::Signature,
            AuthRequired::Proof,
            AuthRequired::Either,
            AuthRequired::Impossible,
        ]
        .iter()
        .map(permissions_to_bits)
        .collect();
        // All distinct
        for i in 0..bs.len() {
            for j in (i + 1)..bs.len() {
                assert_ne!(bs[i], bs[j]);
            }
        }
    }

    #[test]
    fn roots_for_sentinel_when_no_role() {
        let sched = ExpectedBilateral {
            transfers: vec![TransferEntry {
                from: cid(1),
                to: cid(2),
                amount: 50,
            }],
            grants: vec![],
            introduces: vec![],
        };
        let roots_for_unrelated = sched.roots_for(&cid(99), 7);
        // Unrelated cell sees nothing — all sentinels.
        assert_eq!(roots_for_unrelated, BilateralRoots::default());
    }

    #[test]
    fn roots_for_sender_and_receiver_differ() {
        let sched = ExpectedBilateral {
            transfers: vec![TransferEntry {
                from: cid(1),
                to: cid(2),
                amount: 50,
            }],
            grants: vec![],
            introduces: vec![],
        };
        let sender = sched.roots_for(&cid(1), 7);
        let receiver = sched.roots_for(&cid(2), 7);
        // Sender's outbound and receiver's inbound are both non-zero;
        // the other slots are sentinel.
        assert_ne!(sender.outgoing_transfer, [BabyBear::ZERO; 4]);
        assert_eq!(sender.incoming_transfer, [BabyBear::ZERO; 4]);
        assert_eq!(receiver.outgoing_transfer, [BabyBear::ZERO; 4]);
        assert_ne!(receiver.incoming_transfer, [BabyBear::ZERO; 4]);
        // Different salts + peer encodings mean sender_outbound != receiver_inbound
        // even though they fold the same transfer_id.
        assert_ne!(sender.outgoing_transfer, receiver.incoming_transfer);
    }

    #[test]
    fn counts_match_role() {
        let sched = ExpectedBilateral {
            transfers: vec![
                TransferEntry {
                    from: cid(1),
                    to: cid(2),
                    amount: 50,
                },
                TransferEntry {
                    from: cid(1),
                    to: cid(3),
                    amount: 25,
                },
            ],
            grants: vec![],
            introduces: vec![],
        };
        let c1 = sched.counts_for(&cid(1));
        assert_eq!(c1.outbound_transfer, 2);
        assert_eq!(c1.inbound_transfer, 0);
        let c2 = sched.counts_for(&cid(2));
        assert_eq!(c2.outbound_transfer, 0);
        assert_eq!(c2.inbound_transfer, 1);
    }
}
