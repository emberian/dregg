/// Code generator: Rust evaluator.
///
/// Produces a function `{name}_check(params...) -> Result<(), ConstraintError>`
/// that directly evaluates the constraint at runtime.
/// For effects, mutable params are taken as `&mut` and mutations are applied in-place.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, ParamType, RequirementKind, Statement};

fn param_type_tokens(ty: &ParamType) -> TokenStream {
    match ty {
        ParamType::U64 => quote! { u64 },
        ParamType::ByteArray32 => quote! { [u8; 32] },
        ParamType::Set => quote! { &std::collections::HashSet<u64> },
        ParamType::UserDefined(path) => {
            // Parse the stored type path back into tokens
            let ts: TokenStream = path.parse().unwrap_or_else(|_| quote! { u64 });
            ts
        }
    }
}

pub fn generate_rust_evaluator(ir: &ConstraintIr) -> TokenStream {
    let fn_name = format_ident!("{}_check", ir.name);
    let caveat_name_str = ir.name.to_string();

    let params: Vec<TokenStream> = ir
        .params
        .iter()
        .map(|p| {
            let name = &p.name;
            let base_ty = param_type_tokens(&p.ty);
            if p.mutable {
                quote! { #name: &mut #base_ty }
            } else {
                quote! { #name: #base_ty }
            }
        })
        .collect();

    let body = generate_statements_rust(&ir.statements, &caveat_name_str);

    quote! {
        pub fn #fn_name(#(#params),*) -> Result<(), pyana_dsl_runtime::ConstraintError> {
            #body
            Ok(())
        }
    }
}

fn generate_statements_rust(statements: &[Statement], caveat_name: &str) -> TokenStream {
    let stmts: Vec<TokenStream> = statements
        .iter()
        .map(|stmt| generate_statement_rust(stmt, caveat_name))
        .collect();
    quote! { #(#stmts)* }
}

fn generate_statement_rust(stmt: &Statement, caveat_name: &str) -> TokenStream {
    match stmt {
        Statement::Require(req) => {
            match &req.kind {
                RequirementKind::LessEqual { left, right } => {
                    quote! {
                        if !(#left <= #right) {
                            return Err(pyana_dsl_runtime::ConstraintError::CaveatViolation(#caveat_name));
                        }
                    }
                }
                RequirementKind::GreaterEqual { left, right } => {
                    quote! {
                        if !(#left >= #right) {
                            return Err(pyana_dsl_runtime::ConstraintError::CaveatViolation(#caveat_name));
                        }
                    }
                }
                RequirementKind::Equal { left, right } => {
                    quote! {
                        if !(#left == #right) {
                            return Err(pyana_dsl_runtime::ConstraintError::CaveatViolation(#caveat_name));
                        }
                    }
                }
                RequirementKind::NotEqual { left, right } => {
                    quote! {
                        if !(#left != #right) {
                            return Err(pyana_dsl_runtime::ConstraintError::CaveatViolation(#caveat_name));
                        }
                    }
                }
                RequirementKind::Membership { set, element } => {
                    let set_ident = format_ident!("{}", set);
                    let elem_ident = format_ident!("{}", element);
                    quote! {
                        if !#set_ident.contains(&#elem_ident) {
                            return Err(pyana_dsl_runtime::ConstraintError::CaveatViolation(#caveat_name));
                        }
                    }
                }
            }
        }
        Statement::Mutate(mutation) => {
            let target = format_ident!("{}", mutation.target);
            let operand = format_ident!("{}", mutation.operand);
            match mutation.op {
                MutateOp::SubAssign => quote! { *#target -= #operand; },
                MutateOp::AddAssign => quote! { *#target += #operand; },
                MutateOp::Assign => quote! { *#target = #operand; },
            }
        }
        Statement::Match { discriminant, arms } => {
            let disc_ident = format_ident!("{}", discriminant);
            let arm_tokens: Vec<TokenStream> = arms
                .iter()
                .map(|arm| {
                    let body = generate_statements_rust(&arm.body, caveat_name);
                    if arm.variant == "_" {
                        quote! { _ => { #body } }
                    } else {
                        // Use the variant as a path segment
                        let variant_ident = format_ident!("{}", arm.variant);
                        quote! { #variant_ident => { #body } }
                    }
                })
                .collect();
            quote! {
                match #disc_ident {
                    #(#arm_tokens)*
                }
            }
        }
    }
}

/// Generate an effect descriptor function for `#[pyana_effect]` annotated functions.
pub fn generate_effect_descriptor(ir: &ConstraintIr) -> TokenStream {
    if !ir.is_effect {
        return quote! {};
    }

    let fn_name = format_ident!("{}_effect_descriptor", ir.name);
    let effect_name = ir.name.to_string();

    let mutable_params: Vec<TokenStream> = ir
        .mutable_params()
        .iter()
        .map(|p| {
            let name = p.name.to_string();
            quote! { #name }
        })
        .collect();

    let permission = match &ir.required_permission {
        Some(perm) => quote! { Some(#perm) },
        None => quote! { None },
    };

    quote! {
        pub fn #fn_name() -> pyana_dsl_runtime::EffectDescriptor {
            pyana_dsl_runtime::EffectDescriptor {
                name: #effect_name,
                mutable_params: vec![#(#mutable_params),*],
                required_permission: #permission,
            }
        }
    }
}
