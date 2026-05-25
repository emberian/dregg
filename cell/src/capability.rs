use serde::{Deserialize, Serialize};

use crate::facet::{EffectMask, FacetConstraint};
use crate::id::CellId;
use crate::permissions::AuthRequired;
use crate::predicate::WitnessedPredicate;

/// A typed capability caveat — the unified "constraint on cap exercise"
/// shape per PREDICATE-INVENTORY §3.5 + §7.6.
///
/// Existing capability authority predicates (the lattice attenuation
/// shape: `allowed_effects: Option<EffectMask>` on
/// [`CapabilityRef`] / [`AttenuatedCap`], and the order-theoretic
/// `is_narrower_or_equal`/`is_facet_attenuation` checks) stay in their
/// current shape — they are *order-theoretic*, not witness-attached, and
/// PREDICATE-INVENTORY §3.6 case 3 explicitly excludes them from the
/// unification.
///
/// `CapabilityCaveat` is the *additive* surface for cap holders to
/// carry witness-attached predicates on their exercise (e.g. "this cap
/// only fires when you produce a DFA-match proof against the
/// governance-bound route table"), and to declare per-cap
/// `FacetConstraint`s as first-class typed caveats rather than via the
/// bitmask + side-channel constraint shape on `ExtendedFacet`.
///
/// v1 ships the type and a serde round-trip; production wiring (cap
/// exercise reaching for `caveats: Vec<CapabilityCaveat>` on every
/// `CapabilityRef`) is the PREDICATE-INVENTORY §7.6 Phase-6 payoff and
/// stays additive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CapabilityCaveat {
    /// A typed facet constraint (rate limit, max-transfer, allowed
    /// targets, budget). The existing `FacetConstraint` enum is the
    /// canonical shape; this variant carries one of them.
    FacetConstraint(FacetConstraint),
    /// A witness-attached predicate gating cap exercise. The cap
    /// holder must produce a proof that satisfies the registered
    /// verifier kind. Per PREDICATE-INVENTORY §3.5 + §8.3.
    Witnessed(WitnessedPredicate),
}

/// A reference to a capability — an entry in a cell's c-list.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapabilityRef {
    /// Which cell this capability points to.
    pub target: CellId,
    /// Local slot number (position in the c-list).
    pub slot: u32,
    /// What authorization is required to exercise this capability.
    pub permissions: AuthRequired,
    /// Optional capability token hash for verification/revocation.
    pub breadstuff: Option<[u8; 32]>,
    /// Optional expiry height. If set, the capability is considered invalid
    /// after this block height (used for introduction-granted capabilities).
    #[serde(default)]
    pub expires_at: Option<u64>,
    /// Optional facet mask restricting which effect types this capability permits.
    ///
    /// When `None`, all effect types are allowed (unrestricted capability).
    /// When `Some(mask)`, only effect types whose corresponding bit is set in the
    /// mask can be performed via `ExerciseViaCapability` using this capability.
    ///
    /// This implements E-language **facets**: a faceted capability exposes only a
    /// subset of the target cell's interface to the holder. For example, a
    /// transfer-only facet allows sending value but not modifying state fields
    /// or changing permissions.
    ///
    /// Facets compose with attenuation: a delegated faceted capability can only
    /// further restrict (bitwise subset), never amplify.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allowed_effects: Option<EffectMask>,
}

/// An attenuated capability without a slot assignment.
///
/// Produced by [`CapabilitySet::attenuate`]. This represents a capability with narrowed
/// permissions that has not yet been placed into any c-list. The slot is assigned when
/// inserted into a target `CapabilitySet` via [`CapabilitySet::insert_attenuated`].
///
/// This separation prevents a child from inheriting the parent's internal slot numbering,
/// which could leak information about the parent's c-list layout or collide with existing
/// entries in the child's c-list.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttenuatedCap {
    /// Which cell this capability points to.
    pub target: CellId,
    /// What authorization is required to exercise this capability.
    pub permissions: AuthRequired,
    /// Optional capability token hash for verification/revocation.
    pub breadstuff: Option<[u8; 32]>,
    /// Optional expiry height.
    #[serde(default)]
    pub expires_at: Option<u64>,
    /// Optional facet mask (same semantics as CapabilityRef::allowed_effects).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allowed_effects: Option<EffectMask>,
}

/// The c-list: the set of capabilities a cell holds.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapabilitySet {
    refs: Vec<CapabilityRef>,
    next_slot: u32,
}

impl CapabilitySet {
    /// Create an empty capability set.
    pub fn new() -> Self {
        CapabilitySet {
            refs: Vec::new(),
            next_slot: 0,
        }
    }

    /// Grant a capability to reach `target` with the given authorization requirement.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant(&mut self, target: CellId, permissions: AuthRequired) -> Option<u32> {
        self.grant_with_breadstuff(target, permissions, None)
    }

    /// Grant a capability with an optional breadstuff token hash.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_with_breadstuff(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        breadstuff: Option<[u8; 32]>,
    ) -> Option<u32> {
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff,
            expires_at: None,
            allowed_effects: None,
        });
        Some(slot)
    }

    /// Grant a capability with an expiry block height.
    /// After `expires_at`, the capability is considered invalid.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_with_expiry(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        expires_at: u64,
    ) -> Option<u32> {
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff: None,
            expires_at: Some(expires_at),
            allowed_effects: None,
        });
        Some(slot)
    }

    /// Grant a capability preserving ALL fields from a CapabilityRef (breadstuff + expires_at).
    ///
    /// Used during delta application to avoid silently dropping the `expires_at` field.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_full(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        breadstuff: Option<[u8; 32]>,
        expires_at: Option<u64>,
    ) -> Option<u32> {
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff,
            expires_at,
            allowed_effects: None,
        });
        Some(slot)
    }

    /// Grant a faceted capability: restricted to only certain effect types.
    ///
    /// This implements E-language facets: the capability holder can only exercise
    /// the subset of operations described by `effect_mask`. For example, a
    /// `FACET_TRANSFER_ONLY` capability allows sending value but not modifying
    /// state fields or changing permissions.
    ///
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_faceted(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        effect_mask: EffectMask,
    ) -> Option<u32> {
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff: None,
            expires_at: None,
            allowed_effects: Some(effect_mask),
        });
        Some(slot)
    }

    /// Revoke a capability by slot number. Returns true if found and removed.
    pub fn revoke(&mut self, slot: u32) -> bool {
        let before = self.refs.len();
        self.refs.retain(|r| r.slot != slot);
        self.refs.len() < before
    }

    /// Look up a capability by slot number.
    pub fn lookup(&self, slot: u32) -> Option<&CapabilityRef> {
        self.refs.iter().find(|r| r.slot == slot)
    }

    /// Check if this set contains any non-revoked capability referencing the given target.
    ///
    /// A capability with `permissions: Impossible` is treated as revoked/frozen and
    /// does NOT count as a valid access path.
    ///
    /// NOTE: This method does NOT check expiration. Use `has_access_at()` when you
    /// have a current block height available (e.g., during turn execution).
    pub fn has_access(&self, target: &CellId) -> bool {
        self.refs
            .iter()
            .any(|r| &r.target == target && r.permissions != AuthRequired::Impossible)
    }

    /// Check if this set contains any non-revoked, non-expired capability referencing
    /// the given target at the given block height.
    ///
    /// A capability with `permissions: Impossible` is treated as revoked/frozen.
    /// A capability whose `expires_at` is less than `current_height` is treated as expired.
    pub fn has_access_at(&self, target: &CellId, current_height: u64) -> bool {
        self.refs.iter().any(|r| {
            &r.target == target
                && r.permissions != AuthRequired::Impossible
                && r.expires_at.map_or(true, |exp| current_height <= exp)
        })
    }

    /// Attenuate a capability: produce a slot-free [`AttenuatedCap`] with narrower permissions.
    ///
    /// The returned `AttenuatedCap` does NOT carry a slot number. When delegating to a
    /// child, use [`CapabilitySet::insert_attenuated`] to assign the next available slot
    /// in the child's c-list. This prevents a child from inheriting the parent's internal
    /// slot numbering, which could leak information or collide with existing entries.
    ///
    /// Returns `None` if the slot doesn't exist or if `narrower` is not actually
    /// narrower than the existing permissions.
    pub fn attenuate(&self, slot: u32, narrower: AuthRequired) -> Option<AttenuatedCap> {
        let existing = self.lookup(slot)?;
        // The new permission must be at least as restrictive as the old one.
        if !narrower.is_narrower_or_equal(&existing.permissions) {
            return None;
        }
        Some(AttenuatedCap {
            target: existing.target,
            permissions: narrower,
            breadstuff: existing.breadstuff,
            expires_at: existing.expires_at,
            allowed_effects: existing.allowed_effects,
        })
    }

    /// Attenuate a capability with a restricted effect mask (faceting).
    ///
    /// Like `attenuate`, but additionally narrows the allowed effects. The new
    /// `effect_mask` must be a subset of the existing capability's mask (bitwise AND
    /// must equal the new mask). This enforces that facets can only restrict, never
    /// expand, the set of permitted operations.
    ///
    /// Returns `None` if:
    /// - The slot doesn't exist
    /// - `narrower` permissions are not actually narrower
    /// - `effect_mask` attempts to enable bits not present in the original
    pub fn attenuate_faceted(
        &self,
        slot: u32,
        narrower: AuthRequired,
        effect_mask: EffectMask,
    ) -> Option<AttenuatedCap> {
        let existing = self.lookup(slot)?;
        if !narrower.is_narrower_or_equal(&existing.permissions) {
            return None;
        }
        // Enforce monotonic narrowing of the effect mask.
        let parent_mask = existing.allowed_effects.unwrap_or(crate::facet::EFFECT_ALL);
        if !crate::facet::is_facet_attenuation(parent_mask, effect_mask) {
            return None;
        }
        Some(AttenuatedCap {
            target: existing.target,
            permissions: narrower,
            breadstuff: existing.breadstuff,
            expires_at: existing.expires_at,
            allowed_effects: Some(effect_mask),
        })
    }

    /// Monotonically narrow an existing capability in-place — *without*
    /// changing its slot identity.
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §6.3` / the Silver-Vision
    /// AttenuateCapability primitive: today, narrowing a capability
    /// requires `revoke + reissue`, which (a) races against in-flight
    /// exercises, (b) makes the cap *temporarily absent* during the
    /// swap, and (c) loses the c-list slot identity (consumers must
    /// update their references). The structural primitive *narrows
    /// the caveat set / permissions in-place*: slot and `breadstuff`
    /// are preserved, the cap's identity is unchanged, only the
    /// authority shrinks.
    ///
    /// # Soundness
    ///
    /// Strict subset-refinement only — never expansion:
    /// - `narrower` must satisfy `is_narrower_or_equal(existing.permissions)`
    /// - `narrower_effects`, when provided, must be a bitwise subset of
    ///   the existing `allowed_effects` (or of `EFFECT_ALL` if previously
    ///   unbounded)
    /// - `narrower_expiry`, when provided, must be `≤` the existing
    ///   `expires_at` (passing `None` means "leave expiry unchanged" —
    ///   it can never *extend* a finite expiry)
    ///
    /// # Returns
    ///
    /// On success, returns the 32-byte commitment to the *new* (narrower)
    /// CapabilityRef so callers can update c-list audit indices. Returns
    /// `None` if the slot doesn't exist or any narrowing constraint is
    /// violated.
    pub fn attenuate_in_place(
        &mut self,
        slot: u32,
        narrower: AuthRequired,
        narrower_effects: Option<EffectMask>,
        narrower_expiry: Option<u64>,
    ) -> Option<[u8; 32]> {
        // First pass: find slot + validate strict narrowing without mutating.
        let existing = self.lookup(slot)?;
        if !narrower.is_narrower_or_equal(&existing.permissions) {
            return None;
        }
        // Effect-mask narrowing: subset-only.
        let new_effects = match narrower_effects {
            Some(new_mask) => {
                let parent_mask = existing.allowed_effects.unwrap_or(crate::facet::EFFECT_ALL);
                if !crate::facet::is_facet_attenuation(parent_mask, new_mask) {
                    return None;
                }
                Some(new_mask)
            }
            None => existing.allowed_effects,
        };
        // Expiry narrowing: can only shrink.
        let new_expiry = match (existing.expires_at, narrower_expiry) {
            (Some(e), Some(n)) if n > e => return None, // cannot extend a finite expiry
            (None, Some(n)) => Some(n),                 // unbounded → bounded is narrowing
            (existing_exp, None) => existing_exp,       // None means "leave as-is"
            (_, Some(n)) => Some(n),                    // narrower finite expiry
        };

        // Second pass: mutate in place and compute commitment.
        let cap = self.refs.iter_mut().find(|r| r.slot == slot)?;
        cap.permissions = narrower;
        cap.allowed_effects = new_effects;
        cap.expires_at = new_expiry;

        // Commit to the narrowed cap so callers can update c-list audit
        // indices. Uses the same canonical capability-ref hashing as
        // compute_canonical_capability_root (single-element path).
        let mut hasher =
            blake3::Hasher::new_derive_key(crate::commitment::CANONICAL_CAP_ROOT_CONTEXT);
        let one: u64 = 1;
        hasher.update(&one.to_le_bytes());
        crate::commitment::hash_capability_ref_canonical(&mut hasher, cap);
        Some(*hasher.finalize().as_bytes())
    }

    /// Insert an attenuated capability into this set, assigning the next available slot.
    ///
    /// This is the proper way to delegate an attenuated capability to a child: the child's
    /// c-list assigns its own slot number rather than inheriting the parent's.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn insert_attenuated(&mut self, cap: AttenuatedCap) -> Option<u32> {
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        self.refs.push(CapabilityRef {
            target: cap.target,
            slot,
            permissions: cap.permissions,
            breadstuff: cap.breadstuff,
            expires_at: cap.expires_at,
            allowed_effects: cap.allowed_effects,
        });
        Some(slot)
    }

    /// Restore a previously revoked capability by re-inserting it directly.
    /// Used by journal rollback to undo a revocation.
    pub fn restore(&mut self, cap: CapabilityRef) {
        if !self.refs.iter().any(|r| r.slot == cap.slot) {
            self.refs.push(cap);
        }
    }

    /// Number of active capabilities.
    pub fn len(&self) -> usize {
        self.refs.len()
    }

    /// Whether the capability set is empty.
    pub fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    /// Iterate over all capability refs.
    pub fn iter(&self) -> impl Iterator<Item = &CapabilityRef> {
        self.refs.iter()
    }

    /// Mutably iterate over capability refs. Used by the executor's
    /// rollback path to restore in-place narrowings; not for general use
    /// (apps should go through `attenuate_in_place` / `grant`).
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut CapabilityRef> {
        self.refs.iter_mut()
    }

    /// Get all capabilities targeting a specific cell.
    pub fn capabilities_for(&self, target: &CellId) -> Vec<&CapabilityRef> {
        self.refs.iter().filter(|r| &r.target == target).collect()
    }

    /// Look up the first capability referencing the given target.
    /// Returns None if no capability to that target is held.
    pub fn lookup_by_target(&self, target: &CellId) -> Option<&CapabilityRef> {
        self.refs.iter().find(|r| &r.target == target)
    }
}

impl Default for CapabilitySet {
    fn default() -> Self {
        Self::new()
    }
}

/// Returns true if `granted` permissions are equal to or stricter than `held` permissions.
///
/// This enforces the attenuation-only rule: you can only grant permissions that are
/// as restrictive or more restrictive than what you hold. Never amplification.
pub fn is_attenuation(held: &AuthRequired, granted: &AuthRequired) -> bool {
    granted.is_narrower_or_equal(held)
}

#[cfg(test)]
mod attenuate_in_place_tests {
    //! Adversarial tests for `CapabilitySet::attenuate_in_place`.
    //!
    //! Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §6.3` — narrowing must be
    //! strict subset-refinement only. These tests prove that violating
    //! the invariant gets rejected (no widening, no expiry-extension,
    //! no effect-mask widening).
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    #[test]
    fn happy_path_narrows_permissions_and_returns_commitment() {
        let mut caps = CapabilitySet::new();
        let slot = caps.grant(cid(1), AuthRequired::Either).unwrap();
        let h = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, None)
            .expect("narrowing Either -> Signature must succeed");
        assert_eq!(
            caps.lookup(slot).unwrap().permissions,
            AuthRequired::Signature
        );
        // Slot identity unchanged.
        assert_eq!(caps.lookup(slot).unwrap().slot, slot);
        assert_ne!(h, [0u8; 32], "commitment must be non-zero");
    }

    #[test]
    fn rejects_widening_permissions() {
        let mut caps = CapabilitySet::new();
        let slot = caps.grant(cid(1), AuthRequired::Signature).unwrap();
        // Either is *broader* than Signature.
        let result = caps.attenuate_in_place(slot, AuthRequired::Either, None, None);
        assert!(result.is_none(), "must reject widening Signature -> Either");
        // Cap state must be unchanged on rejection.
        assert_eq!(
            caps.lookup(slot).unwrap().permissions,
            AuthRequired::Signature
        );
    }

    #[test]
    fn rejects_unknown_slot() {
        let mut caps = CapabilitySet::new();
        let result = caps.attenuate_in_place(99, AuthRequired::Signature, None, None);
        assert!(result.is_none());
    }

    #[test]
    fn rejects_effect_mask_widening() {
        let mut caps = CapabilitySet::new();
        // Start with a faceted cap allowing only TRANSFER.
        let slot = caps
            .grant_faceted(
                cid(1),
                AuthRequired::Signature,
                crate::facet::EFFECT_TRANSFER,
            )
            .unwrap();
        // Try to widen to TRANSFER | SET_FIELD.
        let result = caps.attenuate_in_place(
            slot,
            AuthRequired::Signature,
            Some(crate::facet::EFFECT_TRANSFER | crate::facet::EFFECT_SET_FIELD),
            None,
        );
        assert!(result.is_none(), "must reject mask widening");
        assert_eq!(
            caps.lookup(slot).unwrap().allowed_effects,
            Some(crate::facet::EFFECT_TRANSFER)
        );
    }

    #[test]
    fn rejects_expiry_extension() {
        let mut caps = CapabilitySet::new();
        let slot = caps
            .grant_with_expiry(cid(1), AuthRequired::Signature, 100)
            .unwrap();
        let result = caps.attenuate_in_place(slot, AuthRequired::Signature, None, Some(200));
        assert!(
            result.is_none(),
            "must reject expiry extension (100 -> 200)"
        );
        assert_eq!(caps.lookup(slot).unwrap().expires_at, Some(100));
    }

    #[test]
    fn allows_expiry_shrinking() {
        let mut caps = CapabilitySet::new();
        let slot = caps
            .grant_with_expiry(cid(1), AuthRequired::Signature, 100)
            .unwrap();
        let h = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, Some(50))
            .expect("expiry shrink 100 -> 50 must succeed");
        assert_eq!(caps.lookup(slot).unwrap().expires_at, Some(50));
        assert_ne!(h, [0u8; 32]);
    }

    #[test]
    fn allows_unbounded_to_bounded_expiry() {
        let mut caps = CapabilitySet::new();
        let slot = caps.grant(cid(1), AuthRequired::Signature).unwrap();
        assert_eq!(caps.lookup(slot).unwrap().expires_at, None);
        let _ = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, Some(1000))
            .expect("None -> Some(1000) is narrowing");
        assert_eq!(caps.lookup(slot).unwrap().expires_at, Some(1000));
    }

    #[test]
    fn allows_effect_mask_narrowing() {
        let mut caps = CapabilitySet::new();
        let slot = caps
            .grant_faceted(
                cid(1),
                AuthRequired::Signature,
                crate::facet::EFFECT_TRANSFER | crate::facet::EFFECT_SET_FIELD,
            )
            .unwrap();
        let _ = caps
            .attenuate_in_place(
                slot,
                AuthRequired::Signature,
                Some(crate::facet::EFFECT_TRANSFER),
                None,
            )
            .expect("mask narrowing to TRANSFER alone must succeed");
        assert_eq!(
            caps.lookup(slot).unwrap().allowed_effects,
            Some(crate::facet::EFFECT_TRANSFER)
        );
    }

    /// Slot identity must be preserved across attenuation — this is
    /// the structural difference between in-place attenuation and the
    /// revoke-and-reissue workaround.
    #[test]
    fn slot_and_target_preserved_across_narrowing() {
        let mut caps = CapabilitySet::new();
        let target = cid(42);
        let slot = caps.grant(target, AuthRequired::Either).unwrap();
        let before_slot = caps.lookup(slot).unwrap().slot;
        let before_target = caps.lookup(slot).unwrap().target;
        let _ = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, None)
            .unwrap();
        assert_eq!(caps.lookup(slot).unwrap().slot, before_slot);
        assert_eq!(caps.lookup(slot).unwrap().target, before_target);
    }

    /// Commitment must change when the narrowed cap differs from the
    /// original — this is what makes c-list audit indices updatable
    /// in a single deterministic step.
    #[test]
    fn commitment_changes_when_cap_narrows() {
        let mut caps = CapabilitySet::new();
        let slot = caps.grant(cid(1), AuthRequired::Either).unwrap();
        // First narrowing.
        let h1 = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, None)
            .unwrap();
        // Second narrowing to identical state — commitment must match.
        let h2 = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, None)
            .unwrap();
        assert_eq!(
            h1, h2,
            "identical narrowed state must produce equal commitments"
        );

        // Further narrowing to Impossible — commitment must differ.
        let h3 = caps
            .attenuate_in_place(slot, AuthRequired::Impossible, None, None)
            .unwrap();
        assert_ne!(
            h1, h3,
            "different narrowed state must produce different commitments"
        );
    }
}
