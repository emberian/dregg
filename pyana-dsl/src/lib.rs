//! Pyana Constraint DSL — proc macro crate.
//!
//! Provides `#[pyana_caveat]` which compiles a constraint function into:
//! - A Rust evaluator (`{name}_check`)
//! - An AIR constraint descriptor (`{name}_air_constraints`)
//! - A Datalog rule fragment (`{name}_datalog`)
//!
//! Phase 1: supports `require!(a <= b)`, `require!(a >= b)`, `require!(a == b)`, `require!(a != b)`
//! with `u64` and `[u8; 32]` parameter types.

extern crate proc_macro;

mod gen_air;
mod gen_datalog;
mod gen_kimchi;
mod gen_rust;
mod ir;
mod parse;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

/// Marks a function as a pyana caveat constraint.
///
/// The function body must consist of `require!(expr)` statements where each
/// `expr` is a binary comparison. The macro expands the function into three
/// generated items:
///
/// - `{name}_check(params...) -> Result<(), ConstraintError>` — runtime evaluator
/// - `{name}_air_constraints() -> AirConstraintSet` — AIR topology descriptor
/// - `{name}_datalog() -> &'static str` — Datalog rule
///
/// # Example
///
/// ```ignore
/// #[pyana_caveat]
/// fn not_after(token_expiry: u64, current_time: u64) {
///     require!(current_time <= token_expiry);
/// }
/// ```
#[proc_macro_attribute]
pub fn pyana_caveat(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);

    let ir = match parse::parse_caveat(&func) {
        Ok(ir) => ir,
        Err(e) => return e.to_compile_error().into(),
    };

    let rust_eval = gen_rust::generate_rust_evaluator(&ir);
    let air_desc = gen_air::generate_air_descriptor(&ir);
    let datalog = gen_datalog::generate_datalog(&ir);
    let kimchi = gen_kimchi::generate_kimchi(&ir);

    let output = quote! {
        #rust_eval
        #air_desc
        #datalog
        #kimchi
    };

    output.into()
}
