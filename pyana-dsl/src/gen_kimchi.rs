/// Code generator: Kimchi gate coefficients (stub for Phase 1).
///
/// This will eventually produce Kimchi custom gate descriptions for
/// Mina-compatible proof generation. For now it's a placeholder that
/// emits a comment-only function.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::ConstraintIr;

pub fn generate_kimchi(_ir: &ConstraintIr) -> TokenStream {
    // Phase 1: stub — Kimchi backend is planned for Phase 3+
    let _ = format_ident!("placeholder");
    quote! {}
}
