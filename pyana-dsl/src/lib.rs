//! Pyana Constraint DSL — proc macro crate.
//!
//! Provides `#[pyana_caveat]` and `#[pyana_effect]` which compile constraint functions into:
//! - A Rust evaluator (`{name}_check`)
//! - An AIR constraint descriptor (`{name}_air_constraints`)
//! - A Datalog rule fragment (`{name}_datalog`)
//! - A Kimchi circuit descriptor (`{name}_kimchi`)
//!
//! Phase 2: adds effects with mutation, Kimchi codegen, multi-constraint composition,
//! set membership, and permission annotations.

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
/// `expr` is a binary comparison or a `.contains()` membership check.
/// The macro expands the function into generated items:
///
/// - `{name}_check(params...) -> Result<(), ConstraintError>` — runtime evaluator
/// - `{name}_air_constraints() -> AirConstraintSet` — AIR topology descriptor
/// - `{name}_datalog() -> &'static str` — Datalog rule
/// - `{name}_kimchi() -> KimchiCircuitDescriptor` — Kimchi gate descriptor
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

/// Marks a function as a pyana effect — a constraint with state mutation.
///
/// Effect functions may contain `&mut` parameters and mutation statements
/// (`*balance -= amount`), in addition to `require!()` checks and `match` arms.
///
/// Supports a `requires` attribute for permission gating:
/// ```ignore
/// #[pyana_effect(requires = "Send")]
/// fn transfer(balance: &mut u64, amount: u64, direction: Direction) {
///     match direction {
///         Direction::Outgoing => {
///             require!(balance >= amount);
///             *balance -= amount;
///         }
///         Direction::Incoming => {
///             *balance += amount;
///         }
///     }
/// }
/// ```
///
/// Generates:
/// - `{name}_check(params...) -> Result<(), ConstraintError>` — evaluator that mutates in-place
/// - `{name}_air_constraints() -> AirConstraintSet` — AIR with old+new columns per mutable param
/// - `{name}_datalog() -> &'static str` — Datalog rule
/// - `{name}_kimchi() -> KimchiCircuitDescriptor` — Kimchi gates
/// - `{name}_effect_descriptor() -> EffectDescriptor` — effect metadata
#[proc_macro_attribute]
pub fn pyana_effect(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);

    // Parse the attribute for `requires = "..."`.
    let required_permission = parse_effect_attr(attr);

    let ir = match parse::parse_effect(&func, required_permission) {
        Ok(ir) => ir,
        Err(e) => return e.to_compile_error().into(),
    };

    let rust_eval = gen_rust::generate_rust_evaluator(&ir);
    let air_desc = gen_air::generate_air_descriptor(&ir);
    let datalog = gen_datalog::generate_datalog(&ir);
    let kimchi = gen_kimchi::generate_kimchi(&ir);
    let effect_desc = gen_rust::generate_effect_descriptor(&ir);

    let output = quote! {
        #rust_eval
        #air_desc
        #datalog
        #kimchi
        #effect_desc
    };

    output.into()
}

/// Parse `#[pyana_effect(requires = "Send")]` attribute.
fn parse_effect_attr(attr: TokenStream) -> Option<String> {
    let attr_str = attr.to_string();
    if attr_str.is_empty() {
        return None;
    }
    // Simple parsing: look for `requires = "..."`
    if let Some(start) = attr_str.find("requires") {
        if let Some(eq_pos) = attr_str[start..].find('=') {
            let after_eq = &attr_str[start + eq_pos + 1..];
            let trimmed = after_eq.trim();
            if trimmed.starts_with('"') {
                let end = trimmed[1..].find('"').unwrap_or(trimmed.len() - 1);
                return Some(trimmed[1..1 + end].to_string());
            }
        }
    }
    None
}
