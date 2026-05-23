/// Code generator: Datalog rule fragment.
///
/// Produces a function `{name}_datalog() -> &'static str` returning a
/// Datalog rule that expresses the same constraint semantics.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, RequirementKind};

pub fn generate_datalog(ir: &ConstraintIr) -> TokenStream {
    let fn_name = format_ident!("{}_datalog", ir.name);
    let rule_name = format!("{}_satisfied", ir.name);

    // Build the rule body: fact lookups + constraint predicates
    let mut body_parts: Vec<String> = Vec::new();

    // Each parameter becomes a fact lookup
    for p in &ir.params {
        let pname = p.name.to_string();
        let capitalized = capitalize(&pname);
        body_parts.push(format!("{}({})", pname, capitalized));
    }

    // Each requirement becomes a built-in predicate
    for req in &ir.requirements {
        let pred = match &req.kind {
            RequirementKind::LessEqual { left, right } => {
                let l = expr_to_datalog_var(left);
                let r = expr_to_datalog_var(right);
                format!("{} <= {}", l, r)
            }
            RequirementKind::GreaterEqual { left, right } => {
                let l = expr_to_datalog_var(left);
                let r = expr_to_datalog_var(right);
                format!("{} >= {}", l, r)
            }
            RequirementKind::Equal { left, right } => {
                let l = expr_to_datalog_var(left);
                let r = expr_to_datalog_var(right);
                format!("{} == {}", l, r)
            }
            RequirementKind::NotEqual { left, right } => {
                let l = expr_to_datalog_var(left);
                let r = expr_to_datalog_var(right);
                format!("{} != {}", l, r)
            }
        };
        body_parts.push(pred);
    }

    let rule = format!("{} :- {}.", rule_name, body_parts.join(", "));

    quote! {
        pub fn #fn_name() -> &'static str {
            #rule
        }
    }
}

/// Convert a Rust expression (expected to be a simple ident) to a Datalog variable name.
fn expr_to_datalog_var(expr: &syn::Expr) -> String {
    // For Phase 1, we only handle simple identifiers
    let token_str = quote::quote!(#expr).to_string();
    capitalize(&token_str)
}

fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}
