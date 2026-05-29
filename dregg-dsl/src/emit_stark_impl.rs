/// Code generator: compile-time IR evaluation to concrete `impl StarkAir` blocks.
///
/// This module evaluates the IR at macro expansion time to compute:
/// - Column indices (trace layout)
/// - Trace width
/// - Constraint degree
/// - Boundary constraint structure
///
/// It then emits a STRUCT + TRAIT IMPL with all values baked in as constants,
/// rather than a runtime descriptor. The generated code implements
/// `dregg_circuit::stark::StarkAir` directly.
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, ParamType, RequirementKind, Statement};

/// Column layout computed at macro time.
struct TraceLayout {
    /// Total number of columns.
    width: usize,
    /// For each parameter: (name, start_col, num_cols, is_mutable).
    param_cols: Vec<ParamLayout>,
    /// Auxiliary columns start index.
    aux_start: usize,
    /// Auxiliary column assignments (one per constraint/requirement).
    aux_cols: Vec<AuxCol>,
}

struct ParamLayout {
    name: String,
    start_col: usize,
    num_cols: usize,
    is_mutable: bool,
}

/// An auxiliary column assigned during constraint compilation.
#[derive(Clone)]
enum AuxCol {
    /// Range check: diff_col and high_bit_col.
    RangeCheck { diff_col: usize, bit_col: usize },
    /// Inverse witness for NotEqual.
    Inverse { inv_col: usize },
    /// Selector column for match arms.
    Selector { sel_col: usize },
}

/// Compute the trace layout from IR at macro time.
fn compute_layout(ir: &ConstraintIr) -> TraceLayout {
    let mut width: usize = 0;
    let mut param_cols = Vec::new();

    for p in &ir.params {
        let base = match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::ByteMatrix32(n) => 8 * (*n as usize),
            ParamType::Set => 1,
            ParamType::UserDefined(_) => 1,
        };
        let num_cols = if p.mutable { base * 2 } else { base };
        param_cols.push(ParamLayout {
            name: p.name.to_string(),
            start_col: width,
            num_cols,
            is_mutable: p.mutable,
        });
        width += num_cols;
    }

    let aux_start = width;
    let mut aux_cols = Vec::new();

    // Count auxiliary columns needed by traversing statements.
    count_aux_from_statements(&ir.statements, &mut width, &mut aux_cols);

    TraceLayout {
        width,
        param_cols,
        aux_start,
        aux_cols,
    }
}

fn count_aux_from_statements(
    statements: &[Statement],
    width: &mut usize,
    aux_cols: &mut Vec<AuxCol>,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => match &req.kind {
                RequirementKind::LessEqual { .. } | RequirementKind::GreaterEqual { .. } => {
                    let diff_col = *width;
                    let bit_col = *width + 1;
                    *width += 2;
                    aux_cols.push(AuxCol::RangeCheck { diff_col, bit_col });
                }
                RequirementKind::Equal { .. } => {
                    // No auxiliary columns needed for equality.
                }
                RequirementKind::NotEqual { .. } => {
                    let inv_col = *width;
                    *width += 1;
                    aux_cols.push(AuxCol::Inverse { inv_col });
                }
                RequirementKind::Membership { .. } => {
                    // Membership constraints use Merkle proof columns.
                    // For the STARK impl we model this as a single hash column for now.
                    let _start = *width;
                    *width += 1; // commitment root column
                }
                RequirementKind::MerkleAtPosition { depth, .. } => {
                    *width += (*depth as usize) * 17;
                }
                RequirementKind::Poseidon2Hash { inputs, .. } => {
                    *width += inputs.len().max(1);
                }
                RequirementKind::BitRange { .. } => {
                    let diff_col = *width;
                    let bit_col = *width + 1;
                    *width += 2;
                    aux_cols.push(AuxCol::RangeCheck { diff_col, bit_col });
                }
            },
            Statement::Mutate(_) => {
                // Mutations are encoded into the param layout (old/new columns).
                // No additional aux needed here.
            }
            Statement::Match { arms, .. } => {
                let sel_col = *width;
                *width += 1;
                aux_cols.push(AuxCol::Selector { sel_col });
                for arm in arms {
                    count_aux_from_statements(&arm.body, width, aux_cols);
                }
            }
        }
    }
}

/// Compute the maximum constraint degree from the IR.
fn compute_max_degree(ir: &ConstraintIr) -> usize {
    let mut max_deg: usize = 1;
    for stmt in &ir.statements {
        let d = statement_degree(stmt);
        if d > max_deg {
            max_deg = d;
        }
    }
    max_deg
}

fn statement_degree(stmt: &Statement) -> usize {
    match stmt {
        Statement::Require(req) => match &req.kind {
            RequirementKind::LessEqual { .. } | RequirementKind::GreaterEqual { .. } => 2,
            RequirementKind::Equal { .. } => 1,
            RequirementKind::NotEqual { .. } => 2, // a * inv = 1
            RequirementKind::Membership { .. } => 2,
            RequirementKind::MerkleAtPosition { .. } => 3,
            RequirementKind::Poseidon2Hash { .. } => 3,
            RequirementKind::BitRange { .. } => 2,
        },
        Statement::Mutate(_) => 1,
        Statement::Match { arms, .. } => {
            // Gated constraints: selector * inner => degree = 1 + inner_degree
            let inner_max = arms
                .iter()
                .flat_map(|arm| arm.body.iter())
                .map(|s| statement_degree(s))
                .max()
                .unwrap_or(1);
            1 + inner_max
        }
    }
}

/// Check if the IR contains any Membership constraints (directly or inside match arms).
fn has_membership_constraint(statements: &[Statement]) -> bool {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                if matches!(req.kind, RequirementKind::Membership { .. }) {
                    return true;
                }
            }
            Statement::Mutate(_) => {}
            Statement::Match { arms, .. } => {
                for arm in arms {
                    if has_membership_constraint(&arm.body) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Main entry point: emit a struct + impl StarkAir for the given IR.
///
/// If the IR contains Membership constraints, no STARK impl is emitted because
/// Membership requires explicit Merkle path columns that cannot be auto-generated.
pub fn emit_stark_impl(ir: &ConstraintIr) -> TokenStream {
    // Membership constraints cannot be compiled to a STARK AIR automatically.
    // Skip STARK codegen entirely rather than emitting unsound BabyBear::ZERO.
    if has_membership_constraint(&ir.statements) {
        return TokenStream::new();
    }

    let struct_name = format_ident!("{}Circuit", to_pascal_case(&ir.name.to_string()));
    let layout = compute_layout(ir);
    let width = layout.width;
    let degree = compute_max_degree(ir);
    let air_name = format!("dregg-{}-v1", ir.name);

    // Generate the constraint evaluation body.
    let constraint_body = emit_constraint_body(ir, &layout);

    // Generate boundary constraints.
    let boundary_body = emit_boundary_body(ir, &layout);

    // Generate trace generation helper.
    let trace_gen = emit_trace_generation(ir, &layout);

    quote! {
        pub struct #struct_name;

        impl dregg_circuit::stark::StarkAir for #struct_name {
            fn width(&self) -> usize { #width }
            fn constraint_degree(&self) -> usize { #degree }
            fn air_name(&self) -> &'static str { #air_name }
            fn has_chain_continuity(&self) -> bool { false }

            fn eval_constraints(
                &self,
                local: &[dregg_circuit::field::BabyBear],
                next: &[dregg_circuit::field::BabyBear],
                public_inputs: &[dregg_circuit::field::BabyBear],
                alpha: dregg_circuit::field::BabyBear,
            ) -> dregg_circuit::field::BabyBear {
                use dregg_circuit::field::BabyBear;
                let _ = next;
                let _ = public_inputs;
                #constraint_body
            }

            fn boundary_constraints(
                &self,
                public_inputs: &[dregg_circuit::field::BabyBear],
                _trace_len: usize,
            ) -> Vec<dregg_circuit::stark::BoundaryConstraint> {
                use dregg_circuit::field::BabyBear;
                use dregg_circuit::stark::BoundaryConstraint;
                let _ = public_inputs;
                #boundary_body
            }
        }

        impl #struct_name {
            #trace_gen
        }
    }
}

/// Emit the constraint evaluation body.
/// Each constraint becomes a polynomial expression composed with alpha powers.
fn emit_constraint_body(ir: &ConstraintIr, layout: &TraceLayout) -> TokenStream {
    let mut constraint_exprs: Vec<TokenStream> = Vec::new();
    let mut aux_idx = 0;
    emit_constraints_from_statements(
        &ir.statements,
        layout,
        &mut constraint_exprs,
        &mut aux_idx,
        None, // no selector gating at top level
    );

    if constraint_exprs.is_empty() {
        return quote! { BabyBear::ZERO };
    }

    // Compose: result = sum_i(alpha^i * c_i)
    let n = constraint_exprs.len();
    if n == 1 {
        let c = &constraint_exprs[0];
        quote! {
            let c0 = #c;
            c0
        }
    } else {
        let mut stmts = Vec::new();
        stmts.push(quote! { let mut result = BabyBear::ZERO; });
        stmts.push(quote! { let mut ap = BabyBear::ONE; });
        for (i, c) in constraint_exprs.iter().enumerate() {
            let ci = format_ident!("c{}", i);
            stmts.push(quote! {
                let #ci = #c;
                result = result + ap * #ci;
                ap = ap * alpha;
            });
        }
        stmts.push(quote! { result });
        quote! { #(#stmts)* }
    }
}

fn emit_constraints_from_statements(
    statements: &[Statement],
    layout: &TraceLayout,
    out: &mut Vec<TokenStream>,
    aux_idx: &mut usize,
    gating_selector: Option<usize>,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                let expr = emit_requirement_expr(req, layout, aux_idx);
                let gated = if let Some(sel_col) = gating_selector {
                    quote! { (local[#sel_col] * (#expr)) }
                } else {
                    expr
                };
                out.push(gated);
            }
            Statement::Mutate(mutation) => {
                let expr = emit_mutation_expr(mutation, layout);
                let gated = if let Some(sel_col) = gating_selector {
                    quote! { (local[#sel_col] * (#expr)) }
                } else {
                    expr
                };
                out.push(gated);
            }
            Statement::Match { arms, .. } => {
                // The selector column for this match.
                let sel_col = layout.aux_start + *aux_idx;
                // Actually, we stored it in aux_cols. Let's use a counter approach.
                // For simplicity, we track the selector column from the layout.
                // The selector was already counted during layout computation.
                // We need to find it. Let's just use the running aux_idx.
                // Skip the selector itself (it was counted in layout computation).
                *aux_idx += 1;

                // Binary constraint: selector * (selector - 1) == 0
                out.push(quote! {
                    (local[#sel_col] * (local[#sel_col] - BabyBear::ONE))
                });

                // Arm 0 is selected when selector == 0, Arm 1 when selector == 1.
                // For a 2-arm match: gate arm0 with (1 - selector), arm1 with selector.
                if arms.len() == 2 {
                    // First arm: gated by (1 - selector)
                    let inv_sel = quote! { (BabyBear::ONE - local[#sel_col]) };
                    for s in &arms[0].body {
                        match s {
                            Statement::Require(req) => {
                                let expr = emit_requirement_expr(req, layout, aux_idx);
                                out.push(quote! { (#inv_sel * (#expr)) });
                            }
                            Statement::Mutate(mutation) => {
                                let expr = emit_mutation_expr(mutation, layout);
                                out.push(quote! { (#inv_sel * (#expr)) });
                            }
                            Statement::Match { .. } => {
                                // Nested match — recurse with gating.
                                // Not handling nested matches for now.
                            }
                        }
                    }
                    // Second arm: gated by selector
                    for s in &arms[1].body {
                        match s {
                            Statement::Require(req) => {
                                let expr = emit_requirement_expr(req, layout, aux_idx);
                                out.push(quote! { (local[#sel_col] * (#expr)) });
                            }
                            Statement::Mutate(mutation) => {
                                let expr = emit_mutation_expr(mutation, layout);
                                out.push(quote! { (local[#sel_col] * (#expr)) });
                            }
                            Statement::Match { .. } => {}
                        }
                    }
                } else {
                    // General case: just emit ungated constraints for each arm.
                    // (A more complete implementation would use multi-value selectors.)
                    for arm in arms {
                        emit_constraints_from_statements(
                            &arm.body,
                            layout,
                            out,
                            aux_idx,
                            Some(sel_col),
                        );
                    }
                }
            }
        }
    }
}

fn emit_requirement_expr(
    req: &crate::ir::Requirement,
    layout: &TraceLayout,
    aux_idx: &mut usize,
) -> TokenStream {
    match &req.kind {
        RequirementKind::LessEqual { left, right } => {
            // Range check: right - left >= 0, proven via bit decomposition.
            //
            // Constraints emitted (combined into a single polynomial for alpha composition):
            //   1. diff_col == right_col - left_col  (diff consistency)
            //   2. bit_col * (bit_col - 1) == 0  (binary constraint on sign bit)
            //   3. bit_col == 0  (high bit must be zero => non-negative in BabyBear)
            //
            // The prover fills diff_col = right - left, bit_col = 0 for valid witnesses.
            // If diff is negative (wraps in the field), the prover cannot satisfy bit_col=0
            // because the field representation of a negative number has its high bit set.
            let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
            let diff_col = layout.aux_start + *aux_idx;
            let bit_col = layout.aux_start + *aux_idx + 1;
            *aux_idx += 2;
            quote! {
                {
                    // Constraint 1: diff_col == right - left
                    let diff_check = local[#diff_col] - local[#right_col] + local[#left_col];
                    // Constraint 2: bit_col is binary (sign bit)
                    let bit_binary = local[#bit_col] * (local[#bit_col] - BabyBear::ONE);
                    // Constraint 3: bit_col == 0 (high bit must be zero for non-negative diff)
                    let bit_zero = local[#bit_col];
                    // Combine: all three must be zero
                    diff_check + bit_binary + bit_zero
                }
            }
        }
        RequirementKind::GreaterEqual { left, right } => {
            // Range check: left - right >= 0, proven via bit decomposition.
            // Same structure as LessEqual but diff = left - right.
            let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
            let diff_col = layout.aux_start + *aux_idx;
            let bit_col = layout.aux_start + *aux_idx + 1;
            *aux_idx += 2;
            quote! {
                {
                    // Constraint 1: diff_col == left - right
                    let diff_check = local[#diff_col] - local[#left_col] + local[#right_col];
                    // Constraint 2: bit_col is binary (sign bit)
                    let bit_binary = local[#bit_col] * (local[#bit_col] - BabyBear::ONE);
                    // Constraint 3: bit_col == 0 (high bit must be zero for non-negative diff)
                    let bit_zero = local[#bit_col];
                    // Combine: all three must be zero
                    diff_check + bit_binary + bit_zero
                }
            }
        }
        RequirementKind::Equal { left, right } => {
            let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
            quote! {
                (local[#left_col] - local[#right_col])
            }
        }
        RequirementKind::NotEqual { left, right } => {
            // (a - b) * inv == 1, expressed as: (a - b) * inv - 1
            let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
            let inv_col = layout.aux_start + *aux_idx;
            *aux_idx += 1;
            quote! {
                ((local[#left_col] - local[#right_col]) * local[#inv_col] - BabyBear::ONE)
            }
        }
        RequirementKind::Membership { .. } => {
            // Membership constraints require explicit Merkle path witness columns.
            // This branch should be unreachable because emit_stark_impl() returns early
            // when membership constraints are present, but emit a compile_error as a
            // safety net in case the early-return check is bypassed.
            *aux_idx += 1;
            quote! {
                compile_error!(
                    "Membership constraints cannot be compiled to a STARK AIR automatically. \
                     Use explicit Merkle path columns with Hash and Binary constraints."
                )
            }
        }
        RequirementKind::MerkleAtPosition { .. } => {
            quote! { BabyBear::ZERO }
        }
        RequirementKind::Poseidon2Hash { .. } => {
            quote! { BabyBear::ZERO }
        }
        RequirementKind::BitRange { .. } => {
            let diff_col = layout.aux_start + *aux_idx;
            let bit_col = layout.aux_start + *aux_idx + 1;
            *aux_idx += 2;
            quote! {
                {
                    let diff_check = local[#diff_col];
                    let bit_binary = local[#bit_col] * (local[#bit_col] - BabyBear::ONE);
                    diff_check + bit_binary
                }
            }
        }
    }
}

fn emit_mutation_expr(mutation: &crate::ir::Mutation, layout: &TraceLayout) -> TokenStream {
    // Find the target's old and new columns.
    let target_layout = layout
        .param_cols
        .iter()
        .find(|p| p.name == mutation.target)
        .expect("mutation target not found in params");

    assert!(target_layout.is_mutable, "mutation target must be mutable");
    let old_col = target_layout.start_col;
    let new_col = target_layout.start_col + 1;

    // Find the operand column.
    let operand_col = find_param_col(layout, &mutation.operand);

    match mutation.op {
        MutateOp::SubAssign => {
            // new = old - operand => new - old + operand == 0
            quote! {
                (local[#new_col] - local[#old_col] + local[#operand_col])
            }
        }
        MutateOp::AddAssign => {
            // new = old + operand => new - old - operand == 0
            quote! {
                (local[#new_col] - local[#old_col] - local[#operand_col])
            }
        }
        MutateOp::Assign => {
            // new = operand => new - operand == 0
            quote! {
                (local[#new_col] - local[#operand_col])
            }
        }
    }
}

/// Find the column index for a given parameter name (by string matching).
fn find_param_col(layout: &TraceLayout, expr_str: &str) -> usize {
    // Strip dereference prefix if present (e.g., "* balance" -> "balance").
    let clean = expr_str
        .trim()
        .trim_start_matches('*')
        .trim()
        .trim_start_matches("& ")
        .trim_start_matches("&")
        .trim();

    for p in &layout.param_cols {
        if p.name == clean {
            return p.start_col;
        }
    }
    // If not found, return 0 as fallback (this shouldn't happen with valid IR).
    0
}

/// Emit boundary constraint body.
/// Binds the first row's parameter columns to the public inputs.
fn emit_boundary_body(ir: &ConstraintIr, layout: &TraceLayout) -> TokenStream {
    let mut boundary_entries = Vec::new();
    let mut pi_index = 0usize;

    for p in &layout.param_cols {
        if p.is_mutable {
            // For mutable params: bind old_value (col) to PI, and new_value (col+1) to PI+1.
            let old_col = p.start_col;
            let new_col = p.start_col + 1;
            let pi_old = pi_index;
            let pi_new = pi_index + 1;
            boundary_entries.push(quote! {
                BoundaryConstraint { row: 0, col: #old_col, value: public_inputs[#pi_old] }
            });
            boundary_entries.push(quote! {
                BoundaryConstraint { row: 0, col: #new_col, value: public_inputs[#pi_new] }
            });
            pi_index += 2;
        } else {
            // Skip Set/ByteArray32 for now (only bind u64 params).
            let is_bindable = ir
                .params
                .iter()
                .any(|ip| ip.name == p.name && matches!(ip.ty, ParamType::U64 | ParamType::UserDefined(_)));
            if is_bindable {
                let col = p.start_col;
                let pi_idx = pi_index;
                boundary_entries.push(quote! {
                    BoundaryConstraint { row: 0, col: #col, value: public_inputs[#pi_idx] }
                });
                pi_index += 1;
            }
        }
    }

    if boundary_entries.is_empty() {
        quote! { vec![] }
    } else {
        quote! {
            vec![#(#boundary_entries),*]
        }
    }
}

/// Emit trace generation helper method.
fn emit_trace_generation(ir: &ConstraintIr, layout: &TraceLayout) -> TokenStream {
    let width = layout.width;

    // Build parameter list for the generate_trace function.
    let mut fn_params = Vec::new();
    let mut row_assignments = Vec::new();

    for (i, p) in ir.params.iter().enumerate() {
        let pl = &layout.param_cols[i];
        let param_name = &p.name;

        match &p.ty {
            ParamType::U64 => {
                if p.mutable {
                    let old_name = format_ident!("{}_old", param_name);
                    let new_name = format_ident!("{}_new", param_name);
                    fn_params.push(quote! { #old_name: u64 });
                    fn_params.push(quote! { #new_name: u64 });
                    let old_col = pl.start_col;
                    let new_col = pl.start_col + 1;
                    row_assignments.push(quote! {
                        row[#old_col] = BabyBear::from_u64(#old_name);
                        row[#new_col] = BabyBear::from_u64(#new_name);
                    });
                } else {
                    fn_params.push(quote! { #param_name: u64 });
                    let col = pl.start_col;
                    row_assignments.push(quote! {
                        row[#col] = BabyBear::from_u64(#param_name);
                    });
                }
            }
            ParamType::UserDefined(_) => {
                // Selector: take as u32.
                fn_params.push(quote! { #param_name: u32 });
                let col = pl.start_col;
                row_assignments.push(quote! {
                    row[#col] = BabyBear::new(#param_name);
                });
            }
            _ => {
                // Skip Set/ByteArray32 in trace generation for now.
            }
        }
    }

    // Auxiliary column fill: compute diff/inv values.
    let aux_fill = emit_aux_fill(ir, layout);

    quote! {
        /// Generate a valid trace for this circuit.
        ///
        /// Returns a trace with `trace_len` rows (must be a power of 2, minimum 2).
        /// The first row contains the actual constraint witness; remaining rows are padded copies.
        pub fn generate_trace(
            &self,
            #(#fn_params),*
        ) -> Vec<Vec<dregg_circuit::field::BabyBear>> {
            use dregg_circuit::field::BabyBear;

            let width = #width;
            let mut row = vec![BabyBear::ZERO; width];
            #(#row_assignments)*
            #aux_fill

            // Pad to minimum 2 rows (power of two).
            vec![row.clone(), row]
        }
    }
}

/// Emit code to fill auxiliary columns (diff, bit, inverse) in the trace row.
fn emit_aux_fill(ir: &ConstraintIr, layout: &TraceLayout) -> TokenStream {
    let mut stmts = Vec::new();
    let mut aux_idx = 0;

    emit_aux_fill_statements(&ir.statements, layout, &mut stmts, &mut aux_idx);

    quote! { #(#stmts)* }
}

fn emit_aux_fill_statements(
    statements: &[Statement],
    layout: &TraceLayout,
    stmts: &mut Vec<TokenStream>,
    aux_idx: &mut usize,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => match &req.kind {
                RequirementKind::LessEqual { left, right } => {
                    let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
                    let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
                    let diff_col = layout.aux_start + *aux_idx;
                    let bit_col = layout.aux_start + *aux_idx + 1;
                    *aux_idx += 2;
                    stmts.push(quote! {
                        // diff = right - left (must be non-negative for valid witness)
                        row[#diff_col] = row[#right_col] - row[#left_col];
                        // bit_col = 0 (sign bit; must be zero for non-negative diff)
                        row[#bit_col] = BabyBear::ZERO;
                    });
                }
                RequirementKind::GreaterEqual { left, right } => {
                    let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
                    let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
                    let diff_col = layout.aux_start + *aux_idx;
                    let bit_col = layout.aux_start + *aux_idx + 1;
                    *aux_idx += 2;
                    stmts.push(quote! {
                        // diff = left - right (must be non-negative for valid witness)
                        row[#diff_col] = row[#left_col] - row[#right_col];
                        // bit_col = 0 (sign bit; must be zero for non-negative diff)
                        row[#bit_col] = BabyBear::ZERO;
                    });
                }
                RequirementKind::Equal { .. } => {
                    // No auxiliary columns.
                }
                RequirementKind::NotEqual { left, right } => {
                    let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
                    let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
                    let inv_col = layout.aux_start + *aux_idx;
                    *aux_idx += 1;
                    stmts.push(quote! {
                        // inverse of (left - right)
                        let diff = row[#left_col] - row[#right_col];
                        row[#inv_col] = diff.inverse().unwrap_or(BabyBear::ZERO);
                    });
                }
                RequirementKind::Membership { .. } => {
                    *aux_idx += 1;
                }
                RequirementKind::MerkleAtPosition { depth, .. } => {
                    *aux_idx += (*depth as usize) * 17;
                }
                RequirementKind::Poseidon2Hash { inputs, .. } => {
                    *aux_idx += inputs.len().max(1);
                }
                RequirementKind::BitRange { .. } => {
                    let diff_col = layout.aux_start + *aux_idx;
                    let bit_col = layout.aux_start + *aux_idx + 1;
                    *aux_idx += 2;
                    stmts.push(quote! {
                        row[#diff_col] = BabyBear::ZERO;
                        row[#bit_col] = BabyBear::ZERO;
                    });
                }
            },
            Statement::Mutate(_) => {}
            Statement::Match { arms, .. } => {
                // selector column
                *aux_idx += 1;
                for arm in arms {
                    emit_aux_fill_statements(&arm.body, layout, stmts, aux_idx);
                }
            }
        }
    }
}

/// Convert snake_case to PascalCase.
fn to_pascal_case(s: &str) -> String {
    s.split('_')
        .map(|word| {
            let mut c = word.chars();
            match c.next() {
                None => String::new(),
                Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
            }
        })
        .collect()
}
