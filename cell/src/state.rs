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
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellState {
    /// 8 user-defined state fields (like Mina's app_state).
    pub fields: [FieldElement; STATE_SLOTS],
    /// Visibility level for each field slot.
    pub field_visibility: [FieldVisibility; STATE_SLOTS],
    /// Hash commitments for non-public fields (BLAKE3 hash of value || nonce).
    /// `None` for Public fields, `Some(hash)` for Committed/SelectivelyDisclosable.
    pub commitments: [Option<[u8; 32]>; STATE_SLOTS],
    /// Monotonically increasing action counter.
    pub nonce: u64,
    /// Computron balance (execution budget).
    pub balance: u64,
    /// Whether all 8 state fields were last set by a verified proof.
    /// Becomes `true` only when ALL 8 fields are set by a single proof-authorized action.
    /// Becomes `false` if any field is modified by a non-proof authorization.
    pub proved_state: bool,
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
    /// Create a fresh cell state with zero fields and the given balance.
    pub fn new(balance: u64) -> Self {
        CellState {
            fields: [FIELD_ZERO; STATE_SLOTS],
            field_visibility: [FieldVisibility::Public; STATE_SLOTS],
            commitments: [None; STATE_SLOTS],
            nonce: 0,
            balance,
            proved_state: false,
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
    pub fn get_field_public(&self, index: usize) -> Option<PublicFieldView> {
        if index >= STATE_SLOTS {
            return None;
        }
        match self.field_visibility[index] {
            FieldVisibility::Public => Some(PublicFieldView::Revealed(self.fields[index])),
            FieldVisibility::Committed | FieldVisibility::SelectivelyDisclosable => {
                match self.commitments[index] {
                    Some(hash) => Some(PublicFieldView::Committed(hash)),
                    None => Some(PublicFieldView::Revealed(self.fields[index])),
                }
            }
        }
    }

    /// Get a state field by index.
    pub fn get_field(&self, index: usize) -> Option<&FieldElement> {
        self.fields.get(index)
    }

    /// Set a state field by index.
    pub fn set_field(&mut self, index: usize, value: FieldElement) -> bool {
        if index < STATE_SLOTS {
            self.fields[index] = value;
            true
        } else {
            false
        }
    }

    /// Increment the nonce by 1.
    pub fn increment_nonce(&mut self) {
        self.nonce = self.nonce.wrapping_add(1);
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
}

impl Default for CellState {
    fn default() -> Self {
        Self::new(0)
    }
}
