/// Code generator: AIR constraint descriptor.
///
/// Produces a function `{name}_air_constraints() -> AirConstraintSet`
/// that returns metadata describing the constraint topology. This is NOT
/// the actual AIR implementation — it's the descriptor from which the AIR
/// can be generated in a separate build step or at runtime.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, ParamType, RequirementKind};

pub fn generate_air_descriptor(ir: &ConstraintIr) -> TokenStream {
    let fn_name = format_ident!("{}_air_constraints", ir.name);
    let constraint_name = ir.name.to_string();

    // Calculate trace width:
    // - Each u64 param takes 1 column
    // - Each [u8; 32] param takes 8 columns (4-byte limbs)
    // - Each comparison requirement adds auxiliary columns:
    //   - <=, >= : 2 columns (diff + high_bit)
    //   - ==     : 0 extra (direct equality)
    //   - !=     : 1 column (inverse witness)
    let mut width: usize = 0;
    for p in &ir.params {
        width += match p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
        };
    }
    for req in &ir.requirements {
        width += match &req.kind {
            RequirementKind::LessEqual { .. } | RequirementKind::GreaterEqual { .. } => 2,
            RequirementKind::Equal { .. } => 0,
            RequirementKind::NotEqual { .. } => 1,
        };
    }

    // Generate constraint descriptors
    let mut col_offset = ir.params.len(); // auxiliary columns start after params
    let constraints: Vec<TokenStream> = ir
        .requirements
        .iter()
        .enumerate()
        .map(|(_i, req)| {
            let c = match &req.kind {
                RequirementKind::LessEqual { left, right } => {
                    let diff_col = col_offset;
                    let bit_col = col_offset + 1;
                    col_offset += 2;
                    // diff = right - left (must be non-negative)
                    let left_str = quote!(#left).to_string();
                    let right_str = quote!(#right).to_string();
                    quote! {
                        pyana_dsl_runtime::Constraint::RangeCheck {
                            desc: concat!("diff = ", #right_str, " - ", #left_str),
                            diff_col: #diff_col,
                            bit_col: #bit_col,
                        }
                    }
                }
                RequirementKind::GreaterEqual { left, right } => {
                    let diff_col = col_offset;
                    let bit_col = col_offset + 1;
                    col_offset += 2;
                    // diff = left - right (must be non-negative)
                    let left_str = quote!(#left).to_string();
                    let right_str = quote!(#right).to_string();
                    quote! {
                        pyana_dsl_runtime::Constraint::RangeCheck {
                            desc: concat!("diff = ", #left_str, " - ", #right_str),
                            diff_col: #diff_col,
                            bit_col: #bit_col,
                        }
                    }
                }
                RequirementKind::Equal { left, right } => {
                    let left_str = quote!(#left).to_string();
                    let right_str = quote!(#right).to_string();
                    quote! {
                        pyana_dsl_runtime::Constraint::Equality {
                            desc: concat!(#left_str, " == ", #right_str),
                        }
                    }
                }
                RequirementKind::NotEqual { left, right } => {
                    let inv_col = col_offset;
                    col_offset += 1;
                    let left_str = quote!(#left).to_string();
                    let right_str = quote!(#right).to_string();
                    quote! {
                        pyana_dsl_runtime::Constraint::NonEquality {
                            desc: concat!(#left_str, " != ", #right_str),
                            inverse_col: #inv_col,
                        }
                    }
                }
            };
            c
        })
        .collect();

    // Determine which params are public inputs (for Phase 1, all are public)
    let public_inputs: Vec<TokenStream> = ir
        .params
        .iter()
        .map(|p| {
            let name_str = p.name.to_string();
            quote! { #name_str }
        })
        .collect();

    quote! {
        pub fn #fn_name() -> pyana_dsl_runtime::AirConstraintSet {
            pyana_dsl_runtime::AirConstraintSet {
                name: #constraint_name,
                width: #width,
                constraints: vec![#(#constraints),*],
                public_inputs: vec![#(#public_inputs),*],
            }
        }
    }
}
