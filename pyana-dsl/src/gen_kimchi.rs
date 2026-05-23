/// Code generator: Kimchi gate descriptors.
///
/// Produces a function `{name}_kimchi() -> KimchiCircuitDescriptor` that
/// returns a description of the Kimchi gates needed to enforce the constraint.
///
/// Gate types:
/// - Equality: Generic gate with `coeffs[0]=1, coeffs[1]=-1` (a - b = 0)
/// - Lte/Gte: diff computation gate + 64 binary gates for bit decomposition + reconstruction
/// - Neq: inverse-existence gate `coeffs[3]=1, coeffs[4]=-1`
/// - Membership: Poseidon gadgets (12 rows per hash level)
/// - SubAssign: `coeffs[0]=1, coeffs[1]=-1, coeffs[2]=-1` (old - amount - new = 0)
/// - AddAssign: `coeffs[0]=1, coeffs[1]=1, coeffs[2]=-1` (old + amount - new = 0)

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, ParamType, RequirementKind, Statement};

pub fn generate_kimchi(ir: &ConstraintIr) -> TokenStream {
    let fn_name = format_ident!("{}_kimchi", ir.name);

    // Calculate public input count (non-mutable params)
    let public_input_count: usize = ir
        .params
        .iter()
        .filter(|p| !p.mutable)
        .map(|p| match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::Set => 1,
            ParamType::UserDefined(_) => 1,
        })
        .sum();

    // Calculate trace width: all params + auxiliary
    let mut trace_width: usize = 0;
    for p in &ir.params {
        let base = match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::Set => 1,
            ParamType::UserDefined(_) => 1,
        };
        if p.mutable {
            trace_width += base * 2;
        } else {
            trace_width += base;
        }
    }

    // Collect gates from statements
    let mut gate_tokens: Vec<TokenStream> = Vec::new();
    collect_kimchi_gates(&ir.statements, &mut gate_tokens, &mut trace_width);

    let gate_count = gate_tokens.len();
    let _ = gate_count;

    quote! {
        pub fn #fn_name() -> pyana_dsl_runtime::KimchiCircuitDescriptor {
            pyana_dsl_runtime::KimchiCircuitDescriptor {
                gates: vec![#(#gate_tokens),*],
                public_input_count: #public_input_count,
                trace_width: #trace_width,
            }
        }
    }
}

fn collect_kimchi_gates(
    statements: &[Statement],
    gates: &mut Vec<TokenStream>,
    trace_width: &mut usize,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => match &req.kind {
                RequirementKind::LessEqual { .. } | RequirementKind::GreaterEqual { .. } => {
                    // Diff computation gate
                    gates.push(quote! {
                        pyana_dsl_runtime::KimchiGate {
                            typ: pyana_dsl_runtime::GateType::Generic,
                            coeffs: vec![1, -1, 0, 0, 0],
                            wires: 2,
                        }
                    });
                    // 64 binary constraint gates for bit decomposition
                    for _ in 0..64 {
                        gates.push(quote! {
                            pyana_dsl_runtime::KimchiGate {
                                typ: pyana_dsl_runtime::GateType::Generic,
                                coeffs: vec![1, 0, -1, 0, 0],
                                wires: 1,
                            }
                        });
                    }
                    // Reconstruction gate (sum of bits * powers of 2 == diff)
                    gates.push(quote! {
                        pyana_dsl_runtime::KimchiGate {
                            typ: pyana_dsl_runtime::GateType::Generic,
                            coeffs: vec![1, -1, 0, 0, 0],
                            wires: 2,
                        }
                    });
                    *trace_width += 66; // diff + 64 bits + reconstruction
                }
                RequirementKind::Equal { .. } => {
                    // Single equality gate: coeffs[0]=1, coeffs[1]=-1
                    gates.push(quote! {
                        pyana_dsl_runtime::KimchiGate {
                            typ: pyana_dsl_runtime::GateType::Generic,
                            coeffs: vec![1, -1, 0, 0, 0],
                            wires: 2,
                        }
                    });
                    *trace_width += 0; // no extra columns needed
                }
                RequirementKind::NotEqual { .. } => {
                    // Inverse-existence gate: coeffs[3]=1, coeffs[4]=-1
                    // Proves (a - b) * inv == 1 where inv is the witness
                    gates.push(quote! {
                        pyana_dsl_runtime::KimchiGate {
                            typ: pyana_dsl_runtime::GateType::Generic,
                            coeffs: vec![0, 0, 0, 1, -1],
                            wires: 3,
                        }
                    });
                    *trace_width += 1; // inverse witness column
                }
                RequirementKind::Membership { .. } => {
                    // Poseidon gadgets: 12 rows per hash level, depth=32
                    let depth = 32;
                    for _ in 0..depth {
                        gates.push(quote! {
                            pyana_dsl_runtime::KimchiGate {
                                typ: pyana_dsl_runtime::GateType::Poseidon,
                                coeffs: vec![],
                                wires: 12,
                            }
                        });
                    }
                    *trace_width += depth * 12; // 12 wires per Poseidon round
                }
            },
            Statement::Mutate(mutation) => {
                match mutation.op {
                    MutateOp::SubAssign => {
                        // old - amount - new == 0
                        // coeffs[0]=1 (old), coeffs[1]=-1 (amount), coeffs[2]=-1 (new)
                        gates.push(quote! {
                            pyana_dsl_runtime::KimchiGate {
                                typ: pyana_dsl_runtime::GateType::Generic,
                                coeffs: vec![1, -1, -1, 0, 0],
                                wires: 3,
                            }
                        });
                    }
                    MutateOp::AddAssign => {
                        // old + amount - new == 0
                        // coeffs[0]=1 (old), coeffs[1]=1 (amount), coeffs[2]=-1 (new)
                        gates.push(quote! {
                            pyana_dsl_runtime::KimchiGate {
                                typ: pyana_dsl_runtime::GateType::Generic,
                                coeffs: vec![1, 1, -1, 0, 0],
                                wires: 3,
                            }
                        });
                    }
                    MutateOp::Assign => {
                        // new == value
                        gates.push(quote! {
                            pyana_dsl_runtime::KimchiGate {
                                typ: pyana_dsl_runtime::GateType::Generic,
                                coeffs: vec![1, -1, 0, 0, 0],
                                wires: 2,
                            }
                        });
                    }
                }
                *trace_width += 0; // mutation columns already counted in param width
            }
            Statement::Match { arms, .. } => {
                // Selector column for one-hot encoding
                *trace_width += 1;
                for arm in arms {
                    collect_kimchi_gates(&arm.body, gates, trace_width);
                }
            }
        }
    }
}
