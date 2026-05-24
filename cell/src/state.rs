use serde::{Deserialize, Serialize};

/// A generic 32-byte field element.
/// Could represent a BabyBear element, a BLAKE3 hash, a scalar, etc.
pub type FieldElement = [u8; 32];

/// The zero field element.
pub const FIELD_ZERO: FieldElement = [0u8; 32];

/// Number of user-defined state slots per cell.
pub const STATE_SLOTS: usize = 8;

/// Visibility level for a cell state field.
///
/// Controls progressive disclosure: fields can be fully public, committed (hidden
/// behind a hash), or selectively disclosable (committed but provable via ZK).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldVisibility {
    /// Value stored in plaintext — anyone can read it.
    Public,
    /// Only a hash commitment is stored publicly. The actual value is private.
    Committed,
    /// Committed, but the holder can produce membership/predicate proofs
    /// over the value without revealing it.
    SelectivelyDisclosable,
}

impl Default for FieldVisibility {
    fn default() -> Self {
        FieldVisibility::Public
    }
}

/// The mutable state of an agent cell.
///
/// Audit P0-1 sealing: `nonce`, `balance`, `proved_state`, and
/// `delegation_epoch` are `pub(crate)` — external code reads them via
/// accessors ([`CellState::nonce`], [`CellState::balance`],
/// [`CellState::proved_state`], [`CellState::delegation_epoch`]) and mutates
/// them only through `apply_balance_change`, `increment_nonce`,
/// `bump_delegation_epoch`, and `set_proved_state`. `fields[]`,
/// `field_visibility[]`, and `commitments[]` remain public arrays because the
/// executor mutates them by index in tight loops.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellState {
    /// 8 user-defined state fields (like Mina's app_state).
    pub fields: [FieldElement; STATE_SLOTS],
    /// Visibility level for each field slot.
    pub field_visibility: [FieldVisibility; STATE_SLOTS],
    /// Hash commitments for non-public fields (BLAKE3 hash of value || nonce).
    /// `None` for Public fields, `Some(hash)` for Committed/SelectivelyDisclosable.
    pub commitments: [Option<[u8; 32]>; STATE_SLOTS],
    /// Monotonically increasing action counter. Sealed (P0-1); mutate via
    /// `increment_nonce`, read via `nonce()`.
    pub(crate) nonce: u64,
    /// Computron balance (execution budget). Sealed (P0-1); mutate via
    /// `apply_balance_change`, read via `balance()`.
    pub(crate) balance: u64,
    /// Whether all 8 state fields were last set by a verified proof.
    /// Becomes `true` only when ALL 8 fields are set by a single proof-authorized action.
    /// Becomes `false` if any field is modified by a non-proof authorization.
    /// Sealed (P0-1); mutate via `set_proved_state`, read via `proved_state()`.
    pub(crate) proved_state: bool,
    /// Delegation epoch counter. Parent cells bump this to signal their children
    /// should refresh their capability snapshots. Children whose snapshot epoch is
    /// behind the parent's current epoch are considered stale.
    /// Sealed (P0-1); mutate via `bump_delegation_epoch`, read via
    /// `delegation_epoch()`.
    #[serde(default)]
    pub(crate) delegation_epoch: u64,
}

/// The public view of a field — either the actual value (if public) or its commitment hash.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PublicFieldView {
    /// The field value is revealed (public).
    Revealed(FieldElement),
    /// The field value is hidden; only the commitment hash is visible.
    Committed([u8; 32]),
}

impl CellState {
    /// Read accessor for `nonce`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use pyana_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.nonce = 42;
    /// ```
    #[inline]
    pub fn nonce(&self) -> u64 {
        self.nonce
    }

    /// Read accessor for `balance`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use pyana_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.balance = u64::MAX;
    /// ```
    #[inline]
    pub fn balance(&self) -> u64 {
        self.balance
    }

    /// Read accessor for `proved_state`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use pyana_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.proved_state = true;
    /// ```
    #[inline]
    pub fn proved_state(&self) -> bool {
        self.proved_state
    }

    /// Read accessor for `delegation_epoch`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use pyana_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.delegation_epoch = 7;
    /// ```
    #[inline]
    pub fn delegation_epoch(&self) -> u64 {
        self.delegation_epoch
    }

    /// Set the `proved_state` flag. Sealed-write accessor (P0-1).
    ///
    /// The executor calls this after applying a proof-authorized action: it
    /// passes `true` only when all 8 fields were set by a single proof, and
    /// `false` when any non-proof authorization touched the cell.
    #[inline]
    pub fn set_proved_state(&mut self, value: bool) {
        self.proved_state = value;
    }

    /// Create a fresh cell state with zero fields and the given balance.
    pub fn new(balance: u64) -> Self {
        CellState {
            fields: [FIELD_ZERO; STATE_SLOTS],
            field_visibility: [FieldVisibility::Public; STATE_SLOTS],
            commitments: [None; STATE_SLOTS],
            nonce: 0,
            balance,
            proved_state: false,
            delegation_epoch: 0,
        }
    }

    /// Set a field's visibility level. If transitioning to Committed or
    /// SelectivelyDisclosable, computes and stores the commitment hash.
    /// The `commitment_nonce` is mixed into the hash to prevent rainbow attacks.
    pub fn set_field_visibility(
        &mut self,
        index: usize,
        visibility: FieldVisibility,
        commitment_nonce: u64,
    ) -> bool {
        if index >= STATE_SLOTS {
            return false;
        }
        self.field_visibility[index] = visibility;
        match visibility {
            FieldVisibility::Public => {
                self.commitments[index] = None;
            }
            FieldVisibility::Committed | FieldVisibility::SelectivelyDisclosable => {
                self.commitments[index] = Some(Self::compute_commitment(
                    &self.fields[index],
                    commitment_nonce,
                ));
            }
        }
        true
    }

    /// Compute a BLAKE3 commitment: H(value || nonce_bytes).
    fn compute_commitment(value: &FieldElement, nonce: u64) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(value);
        hasher.update(&nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Get the public view of a field: returns the value if Public, or the
    /// commitment hash if Committed/SelectivelyDisclosable.
    ///
    /// Audit P1-2: previously, if the visibility was `Committed` or
    /// `SelectivelyDisclosable` but the stored `commitments[index]` was `None`
    /// (because `set_field` invalidated the stale hash), this function fell
    /// through to `PublicFieldView::Revealed(self.fields[index])` and silently
    /// leaked the supposedly-private value. We now return a sentinel
    /// `PublicFieldView::Committed([0u8; 32])` instead — callers MUST treat
    /// the zero-hash as "commitment is stale; ask the holder to re-commit
    /// with `set_field_visibility`," not as a free plaintext disclosure.
    pub fn get_field_public(&self, index: usize) -> Option<PublicFieldView> {
        if index >= STATE_SLOTS {
            return None;
        }
        match self.field_visibility[index] {
            FieldVisibility::Public => Some(PublicFieldView::Revealed(self.fields[index])),
            FieldVisibility::Committed | FieldVisibility::SelectivelyDisclosable => {
                match self.commitments[index] {
                    Some(hash) => Some(PublicFieldView::Committed(hash)),
                    // Stale commitment after `set_field`: refuse to reveal the
                    // plaintext. Return the all-zero sentinel so the public
                    // view is non-informative until the holder re-commits.
                    None => Some(PublicFieldView::Committed([0u8; 32])),
                }
            }
        }
    }

    /// Get a state field by index.
    pub fn get_field(&self, index: usize) -> Option<&FieldElement> {
        self.fields.get(index)
    }

    /// Set a state field by index.
    ///
    /// Invalidates any stale commitment for this field. Callers that need the
    /// commitment to remain valid must call `set_field_visibility` with a fresh
    /// nonce after updating the value.
    pub fn set_field(&mut self, index: usize, value: FieldElement) -> bool {
        if index < STATE_SLOTS {
            self.fields[index] = value;
            // Invalidate stale commitment — old hash no longer matches new value.
            if self.commitments[index].is_some() {
                self.commitments[index] = None;
            }
            true
        } else {
            false
        }
    }

    /// Increment the nonce by 1, returning `true` on success and `false` on
    /// overflow.
    ///
    /// Audit P2-2: previously used `wrapping_add`, which would silently wrap
    /// after 2^64 increments and re-enable replay of historical actions.
    /// Callers must check the return value and refuse to proceed on `false`.
    #[must_use = "nonce overflow must be handled; ignoring the return value re-introduces P2-2"]
    pub fn increment_nonce(&mut self) -> bool {
        match self.nonce.checked_add(1) {
            Some(n) => {
                self.nonce = n;
                true
            }
            None => false,
        }
    }

    /// Apply a balance change (positive or negative). Returns false on underflow.
    pub fn apply_balance_change(&mut self, delta: i64) -> bool {
        if delta >= 0 {
            match self.balance.checked_add(delta as u64) {
                Some(new_bal) => {
                    self.balance = new_bal;
                    true
                }
                None => false,
            }
        } else {
            let abs = delta.unsigned_abs();
            if self.balance >= abs {
                self.balance -= abs;
                true
            } else {
                false
            }
        }
    }

    /// Bump the delegation epoch (signals children to refresh).
    ///
    /// Audit P2-2: previously used `wrapping_add`. Returns `false` on overflow;
    /// in practice 2^64 epoch bumps is unreachable but a wrap would let stale
    /// delegations regain freshness.
    #[must_use = "delegation epoch overflow must be handled"]
    pub fn bump_delegation_epoch(&mut self) -> bool {
        match self.delegation_epoch.checked_add(1) {
            Some(e) => {
                self.delegation_epoch = e;
                true
            }
            None => false,
        }
    }
}

impl Default for CellState {
    fn default() -> Self {
        Self::new(0)
    }
}
