/// Code generator: Datalog rule fragment.
///
/// Produces a function `{name}_datalog() -> &'static str` returning a
/// Datalog rule that expresses the same constraint semantics.
///
/// For effects, mutations become output facts (e.g., `next_balance(B - Amount)`).
/// For membership, emits `member_of(X, Set)`.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, RequirementKind, Statement};

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

    // Collect predicates from all statements
    collect_datalog_predicates(&ir.statements, &mut body_parts);

    let rule = format!("{} :- {}.", rule_name, body_parts.join(", "));

    quote! {
        pub fn #fn_name() -> &'static str {
            #rule
        }
    }
}

fn collect_datalog_predicates(statements: &[Statement], body_parts: &mut Vec<String>) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
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
                    RequirementKind::Membership { set, element } => {
                        let s = capitalize(set);
                        let e = capitalize(element);
                        format!("member_of({}, {})", e, s)
                    }
                };
                body_parts.push(pred);
            }
            Statement::Mutate(mutation) => {
                let target = capitalize(&mutation.target);
                let operand = capitalize(&mutation.operand);
                let next = match mutation.op {
                    MutateOp::SubAssign => format!("next_{}({} - {})", mutation.target, target, operand),
                    MutateOp::AddAssign => format!("next_{}({} + {})", mutation.target, target, operand),
                    MutateOp::Assign => format!("next_{}({})", mutation.target, operand),
                };
                body_parts.push(next);
            }
            Statement::Match { discriminant, arms } => {
                // Each arm becomes a separate clause; for simplicity, inline all
                let disc = capitalize(discriminant);
                for arm in arms {
                    if arm.variant != "_" {
                        body_parts.push(format!("variant({}, {})", disc, arm.variant));
                    }
                    collect_datalog_predicates(&arm.body, body_parts);
                }
            }
        }
    }
}

/// Convert a Rust expression (expected to be a simple ident) to a Datalog variable name.
fn expr_to_datalog_var(expr: &syn::Expr) -> String {
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
