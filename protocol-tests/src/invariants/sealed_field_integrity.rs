//! Sealed-field integrity invariant. **STUB.**
//!
//! > No external code path mutates `Cell::id`, `public_key`, `token_id`,
//! > `nonce`, `balance`, `proved_state`, or `delegation_epoch` outside the
//! > accessor methods.
//!
//! ## What this test would check
//!
//! This is type-system-enforced today via `pub(crate)` visibility on the
//! affected fields. The corresponding "test" is a battery of
//! `compile_fail` doctests showing that external mutation attempts do
//! NOT compile. They live today as inline doctests on the field accessor
//! methods in `cell/src/state.rs` and `cell/src/cell.rs`.
//!
//! In this crate we'd add `compile_fail` doctests of the shape:
//!
//! ```compile_fail
//! use pyana_cell::Cell;
//! fn evil(c: &mut Cell) {
//!     c.public_key = [0; 32]; // SHOULD NOT COMPILE
//! }
//! ```
//!
//! ...for each sealed field. The `proptest!` block analogy doesn't apply
//! because there's no runtime input to vary — the property is "this code
//! does not compile, ever, across all possible inputs."
//!
//! ## Why stubbed
//!
//! Doctests need to live on a public item so rustdoc picks them up. We'd
//! want to add a small public type here (e.g. `SealedFieldCompileFail`)
//! whose doc string carries the 7 `compile_fail` blocks. That's
//! mechanical to write but adds a public surface item which deserves
//! deliberate naming — punted to next session.

use crate::Invariant;

pub struct SealedFieldIntegrity;

impl Invariant for SealedFieldIntegrity {
    const NAME: &'static str = "sealed_field_integrity";
    const DESCRIPTION: &'static str =
        "external code cannot mutate Cell::id/public_key/token_id or CellState::nonce/balance/proved_state/delegation_epoch";
}

#[test]
#[ignore = "stubbed: implement in next session — implement as compile_fail doctests, see module docs"]
fn sealed_field_integrity_holds() {
    unimplemented!(
        "Add compile_fail doctests demonstrating each of the 7 sealed fields rejects external mutation."
    );
}
