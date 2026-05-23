/// Code generator: AIR constraint descriptor.
///
/// Produces a function `{name}_air_constraints() -> AirConstraintSet`
/// that returns metadata describing the constraint topology. This is NOT
/// the actual AIR implementation — it's the descriptor from which the AIR
/// can be generated in a separate build step or at runtime.
///
/// For effects with mutations:
/// - Each mutable param gets 2 columns (old_value + new_value)
/// - Constraints enforce: new = old +/- operand
///
/// For set membership:
/// - Emits a MerkleMembership constraint (position bits + hash chain + root binding)
///
/// Multi-constraint composition:
/// - Total trace width = sum of all sub-constraint widths + shared columns
/// - Constraints combined via random linear combination (alpha^i * constraint_i)

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, ParamType, RequirementKind, Statement};

pub fn generate_air_descriptor(ir: &ConstraintIr) -> TokenStream {
    let fn_name = format_ident!("{}_air_constraints", ir.name);
    let constraint_name = ir.name.to_string();

    // Calculate trace width:
    // - Each immutable u64 param takes 1 column
    // - Each mutable u64 param takes 2 columns (old + new)
    // - Each [u8; 32] param takes 8 columns (4-byte limbs)
    // - Each Set param takes 1 column (the commitment root)
    // - Each comparison requirement adds auxiliary columns
    // - Each mutation adds columns for the operand
    // - Each membership adds Merkle proof columns (depth * 2 + position bits)
    let mut width: usize = 0;
    for p in &ir.params {
        let base = match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::Set => 1, // Merkle root commitment
            ParamType::UserDefined(_) => 1, // selector column for enums
        };
        if p.mutable {
            width += base * 2; // old + new
        } else {
            width += base;
        }
    }

    // Gather constraints from all statements
    let mut constraints_tokens: Vec<TokenStream> = Vec::new();
    let mut aux_width: usize = 0;
    collect_air_constraints(&ir.statements, &mut constraints_tokens, &mut aux_width);
    width += aux_width;

    // Public inputs: all non-mutable params
    let public_inputs: Vec<TokenStream> = ir
        .params
        .iter()
        .filter(|p| !p.mutable)
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
                constraints: vec![#(#constraints_tokens),*],
                public_inputs: vec![#(#public_inputs),*],
            }
        }
    }
}

fn collect_air_constraints(
    statements: &[Statement],
    out: &mut Vec<TokenStream>,
    aux_width: &mut usize,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                let c = match &req.kind {
                    RequirementKind::LessEqual { left, right } => {
                        let diff_col = *aux_width;
                        let bit_col = *aux_width + 1;
                        *aux_width += 2;
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
                        let diff_col = *aux_width;
                        let bit_col = *aux_width + 1;
                        *aux_width += 2;
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
                        let inv_col = *aux_width;
                        *aux_width += 1;
                        let left_str = quote!(#left).to_string();
                        let right_str = quote!(#right).to_string();
                        quote! {
                            pyana_dsl_runtime::Constraint::NonEquality {
                                desc: concat!(#left_str, " != ", #right_str),
                                inverse_col: #inv_col,
                            }
                        }
                    }
                    RequirementKind::Membership { set, element } => {
                        // Merkle membership: 32 position bits + 32 hash columns + root
                        // = 65 auxiliary columns for a depth-32 tree
                        let merkle_start = *aux_width;
                        let depth: usize = 32;
                        *aux_width += depth * 2 + 1; // position bits + sibling hashes + root check
                        let set_str = set.clone();
                        let elem_str = element.clone();
                        let depth_lit = depth;
                        let _ = merkle_start; // used by runtime
                        quote! {
                            pyana_dsl_runtime::Constraint::MerkleMembership {
                                desc: concat!(#elem_str, " in ", #set_str),
                                tree_depth: #depth_lit,
                                start_col: #merkle_start,
                            }
                        }
                    }
                };
                out.push(c);
            }
            Statement::Mutate(mutation) => {
                let target_str = mutation.target.clone();
                let operand_str = mutation.operand.clone();
                let old_col = *aux_width;
                let new_col = *aux_width + 1;
                *aux_width += 2;
                let op_str = match mutation.op {
                    MutateOp::SubAssign => "sub_assign",
                    MutateOp::AddAssign => "add_assign",
                    MutateOp::Assign => "assign",
                };
                out.push(quote! {
                    pyana_dsl_runtime::Constraint::Transition {
                        desc: concat!(#target_str, " ", #op_str, " ", #operand_str),
                        old_col: #old_col,
                        new_col: #new_col,
                    }
                });
            }
            Statement::Match { arms, .. } => {
                // Each arm contributes its own constraints; the selector adds 1 column
                *aux_width += 1; // selector column
                for arm in arms {
                    collect_air_constraints(&arm.body, out, aux_width);
                }
            }
        }
    }
}
