/// Code generator: Rust evaluator.
///
/// Produces a function `{name}_check(params...) -> Result<(), ConstraintError>`
/// that directly evaluates the constraint at runtime.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, RequirementKind};

pub fn generate_rust_evaluator(ir: &ConstraintIr) -> TokenStream {
    let fn_name = format_ident!("{}_check", ir.name);
    let caveat_name_str = ir.name.to_string();

    let params: Vec<TokenStream> = ir
        .params
        .iter()
        .map(|p| {
            let name = &p.name;
            match p.ty {
                crate::ir::ParamType::U64 => quote! { #name: u64 },
                crate::ir::ParamType::ByteArray32 => quote! { #name: [u8; 32] },
            }
        })
        .collect();

    let checks: Vec<TokenStream> = ir
        .requirements
        .iter()
        .map(|req| {
            let (left, right, op_tokens) = match &req.kind {
                RequirementKind::LessEqual { left, right } => (left, right, quote! { <= }),
                RequirementKind::GreaterEqual { left, right } => (left, right, quote! { >= }),
                RequirementKind::Equal { left, right } => (left, right, quote! { == }),
                RequirementKind::NotEqual { left, right } => (left, right, quote! { != }),
            };
            quote! {
                if !(#left #op_tokens #right) {
                    return Err(pyana_dsl_runtime::ConstraintError::CaveatViolation(#caveat_name_str));
                }
            }
        })
        .collect();

    quote! {
        pub fn #fn_name(#(#params),*) -> Result<(), pyana_dsl_runtime::ConstraintError> {
            #(#checks)*
            Ok(())
        }
    }
}
