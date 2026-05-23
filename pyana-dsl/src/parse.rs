/// Parser: converts a syn-parsed function into our constraint IR.
///
/// Supports:
/// - Function parameters with types `u64`, `[u8; 32]`, or `&mut u64`
/// - Body containing `require!(expr)` macro invocations
/// - `*target -= operand` / `*target += operand` mutations (for effects)
/// - `match direction { ... }` arms
/// - `require!(set.contains(x))` membership checks

use proc_macro2::Span;
use syn::{spanned::Spanned, BinOp, Expr, FnArg, ItemFn, Pat, Stmt, Type};

use crate::ir::{
    ConstraintIr, MatchArm, MutateOp, Mutation, Param, ParamType, Requirement, RequirementKind,
    Statement,
};

/// Parse a `#[pyana_caveat]` function — pure requirements, no mutations.
pub fn parse_caveat(func: &ItemFn) -> Result<ConstraintIr, syn::Error> {
    parse_constraint(func, false, None)
}

/// Parse a `#[pyana_effect]` function — may contain mutations.
pub fn parse_effect(
    func: &ItemFn,
    required_permission: Option<String>,
) -> Result<ConstraintIr, syn::Error> {
    parse_constraint(func, true, required_permission)
}

fn parse_constraint(
    func: &ItemFn,
    is_effect: bool,
    required_permission: Option<String>,
) -> Result<ConstraintIr, syn::Error> {
    let name = func.sig.ident.clone();
    let params = parse_params(func, is_effect)?;
    let statements = parse_body_statements(func, is_effect)?;

    if statements.is_empty() {
        return Err(syn::Error::new(
            func.block.span(),
            "pyana constraint function must contain at least one require!() or mutation statement",
        ));
    }

    Ok(ConstraintIr {
        name,
        params,
        statements,
        is_effect,
        required_permission,
    })
}

fn parse_params(func: &ItemFn, allow_mut: bool) -> Result<Vec<Param>, syn::Error> {
    let mut params = Vec::new();
    for arg in &func.sig.inputs {
        match arg {
            FnArg::Typed(pat_type) => {
                let ident = match pat_type.pat.as_ref() {
                    Pat::Ident(pi) => pi.ident.clone(),
                    _ => {
                        return Err(syn::Error::new(
                            pat_type.pat.span(),
                            "pyana constraint parameters must be simple identifiers",
                        ));
                    }
                };

                // Check for `&mut T` reference pattern
                let (ty, mutable) = parse_param_type(&pat_type.ty, allow_mut)?;
                params.push(Param {
                    name: ident,
                    ty,
                    mutable,
                });
            }
            FnArg::Receiver(_) => {
                return Err(syn::Error::new(
                    arg.span(),
                    "pyana constraint functions cannot have self parameters",
                ));
            }
        }
    }
    Ok(params)
}

fn parse_param_type(ty: &Type, allow_mut: bool) -> Result<(ParamType, bool), syn::Error> {
    match ty {
        Type::Reference(tr) => {
            if tr.mutability.is_some() {
                if !allow_mut {
                    return Err(syn::Error::new(
                        tr.span(),
                        "&mut parameters are only allowed in #[pyana_effect] functions",
                    ));
                }
                let inner_ty = parse_inner_type(&tr.elem)?;
                Ok((inner_ty, true))
            } else {
                // Immutable reference — treat as by-value for type purposes
                let inner_ty = parse_inner_type(&tr.elem)?;
                Ok((inner_ty, false))
            }
        }
        _ => {
            let inner_ty = parse_inner_type(ty)?;
            Ok((inner_ty, false))
        }
    }
}

fn parse_inner_type(ty: &Type) -> Result<ParamType, syn::Error> {
    match ty {
        Type::Path(tp) => {
            let seg = tp
                .path
                .segments
                .last()
                .ok_or_else(|| syn::Error::new(tp.path.span(), "empty type path"))?;
            if seg.ident == "u64" {
                Ok(ParamType::U64)
            } else if seg.ident == "Set" || seg.ident == "HashSet" || seg.ident == "BTreeSet" {
                Ok(ParamType::Set)
            } else {
                // User-defined type (enums like Direction)
                let full_path = quote::quote!(#tp).to_string();
                Ok(ParamType::UserDefined(full_path))
            }
        }
        Type::Array(_) => {
            // Accept [u8; 32]
            Ok(ParamType::ByteArray32)
        }
        _ => Err(syn::Error::new(
            ty.span(),
            "unsupported type in pyana constraint (supports u64, [u8; 32], Set<T>, &mut u64)",
        )),
    }
}

fn parse_body_statements(func: &ItemFn, is_effect: bool) -> Result<Vec<Statement>, syn::Error> {
    parse_stmts(&func.block.stmts, is_effect)
}

fn parse_stmts(stmts: &[Stmt], is_effect: bool) -> Result<Vec<Statement>, syn::Error> {
    let mut statements = Vec::new();

    for stmt in stmts {
        match stmt {
            Stmt::Macro(sm) => {
                if is_require_macro(&sm.mac) {
                    let req = parse_require_macro(&sm.mac)?;
                    statements.push(Statement::Require(req));
                } else {
                    return Err(syn::Error::new(
                        sm.mac.path.span(),
                        "only require!() macros are supported in pyana constraint bodies",
                    ));
                }
            }
            Stmt::Expr(expr, _semi) => {
                if let Some(parsed) = try_parse_statement_expr(expr, is_effect)? {
                    statements.push(parsed);
                } else {
                    return Err(syn::Error::new(
                        expr.span(),
                        "unsupported expression in pyana constraint body",
                    ));
                }
            }
            Stmt::Local(_) => {
                // Allow let bindings in effects (ignore them in IR for now)
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "unsupported statement in pyana constraint body",
                ));
            }
        }
    }

    Ok(statements)
}

fn try_parse_statement_expr(
    expr: &Expr,
    is_effect: bool,
) -> Result<Option<Statement>, syn::Error> {
    // Check for require!() macro
    if let Expr::Macro(em) = expr {
        if is_require_macro(&em.mac) {
            let req = parse_require_macro(&em.mac)?;
            return Ok(Some(Statement::Require(req)));
        }
    }

    // Check for mutation: `*target -= operand` or `*target += operand`
    if is_effect {
        if let Some(mutation) = try_parse_mutation(expr)? {
            return Ok(Some(Statement::Mutate(mutation)));
        }
    }

    // Check for match expression
    if let Expr::Match(em) = expr {
        let match_stmt = parse_match_expr(em, is_effect)?;
        return Ok(Some(match_stmt));
    }

    Ok(None)
}

fn try_parse_mutation(expr: &Expr) -> Result<Option<Mutation>, syn::Error> {
    if let Expr::Assign(assign) = expr {
        // Handle compound assignment via `*balance -= amount` which parses as Assign
        // with the left side being a Unary(Deref, ident)
        if let Expr::Unary(syn::ExprUnary {
            op: syn::UnOp::Deref(_),
            expr: inner,
            ..
        }) = assign.left.as_ref()
        {
            let target = expr_to_ident_string(inner)?;
            // The right side should be `target - operand` or `target + operand`
            if let Expr::Binary(bin) = assign.right.as_ref() {
                let operand = expr_to_ident_string(&bin.right)?;
                let op = match &bin.op {
                    BinOp::Sub(_) => MutateOp::SubAssign,
                    BinOp::Add(_) => MutateOp::AddAssign,
                    _ => {
                        return Err(syn::Error::new(
                            bin.op.span(),
                            "unsupported mutation operator (use -= or +=)",
                        ))
                    }
                };
                return Ok(Some(Mutation {
                    target,
                    op,
                    operand,
                }));
            }
            // Plain assignment: `*x = value`
            let operand = expr_to_ident_string(&assign.right)?;
            return Ok(Some(Mutation {
                target,
                op: MutateOp::Assign,
                operand,
            }));
        }
    }

    // Handle AssignOp expressions: `*balance -= amount`
    if let Expr::Binary(bin) = expr {
        match &bin.op {
            BinOp::SubAssign(_) | BinOp::AddAssign(_) => {
                if let Expr::Unary(syn::ExprUnary {
                    op: syn::UnOp::Deref(_),
                    expr: inner,
                    ..
                }) = bin.left.as_ref()
                {
                    let target = expr_to_ident_string(inner)?;
                    let operand = expr_to_ident_string(&bin.right)?;
                    let op = match &bin.op {
                        BinOp::SubAssign(_) => MutateOp::SubAssign,
                        BinOp::AddAssign(_) => MutateOp::AddAssign,
                        _ => unreachable!(),
                    };
                    return Ok(Some(Mutation {
                        target,
                        op,
                        operand,
                    }));
                }
            }
            _ => {}
        }
    }

    Ok(None)
}

fn parse_match_expr(em: &syn::ExprMatch, is_effect: bool) -> Result<Statement, syn::Error> {
    let discriminant = expr_to_ident_string(&em.expr)?;
    let mut arms = Vec::new();

    for arm in &em.arms {
        let variant = pat_to_variant_string(&arm.pat)?;
        let pattern_tokens = quote::quote!(#(arm.pat)).to_string();
        // Store the actual pattern as tokens for faithful Rust codegen
        let pat = &arm.pat;
        let pat_tokens = quote::quote!(#pat).to_string();
        let body_stmts = match arm.body.as_ref() {
            Expr::Block(block) => parse_stmts(&block.block.stmts, is_effect)?,
            other => {
                // Single expression arm
                let mut stmts = Vec::new();
                if let Some(s) = try_parse_statement_expr(other, is_effect)? {
                    stmts.push(s);
                }
                stmts
            }
        };
        arms.push(MatchArm {
            variant,
            pattern_tokens: pat_tokens,
            body: body_stmts,
        });
    }

    Ok(Statement::Match {
        discriminant,
        arms,
    })
}

fn pat_to_variant_string(pat: &Pat) -> Result<String, syn::Error> {
    match pat {
        Pat::Ident(pi) => Ok(pi.ident.to_string()),
        Pat::Path(pp) => {
            let seg = pp
                .path
                .segments
                .last()
                .ok_or_else(|| syn::Error::new(pp.path.span(), "empty path pattern"))?;
            Ok(seg.ident.to_string())
        }
        Pat::TupleStruct(pts) => {
            let seg = pts
                .path
                .segments
                .last()
                .ok_or_else(|| syn::Error::new(pts.path.span(), "empty path pattern"))?;
            Ok(seg.ident.to_string())
        }
        Pat::Wild(_) => Ok("_".to_string()),
        _ => Err(syn::Error::new(
            pat.span(),
            "unsupported pattern in match arm (use simple variant names)",
        )),
    }
}

fn expr_to_ident_string(expr: &Expr) -> Result<String, syn::Error> {
    match expr {
        Expr::Path(ep) => {
            let seg = ep
                .path
                .segments
                .last()
                .ok_or_else(|| syn::Error::new(ep.path.span(), "empty path"))?;
            Ok(seg.ident.to_string())
        }
        Expr::Lit(lit) => Ok(quote::quote!(#lit).to_string()),
        _ => {
            // Fallback: use the token representation
            Ok(quote::quote!(#expr).to_string())
        }
    }
}

fn is_require_macro(mac: &syn::Macro) -> bool {
    mac.path
        .segments
        .last()
        .is_some_and(|seg| seg.ident == "require")
}

fn parse_require_macro(mac: &syn::Macro) -> Result<Requirement, syn::Error> {
    let expr: Expr = mac.parse_body()?;
    classify_expr(&expr)
}

fn classify_expr(expr: &Expr) -> Result<Requirement, syn::Error> {
    match expr {
        Expr::Binary(bin) => {
            let kind = match &bin.op {
                BinOp::Le(_) => RequirementKind::LessEqual {
                    left: *bin.left.clone(),
                    right: *bin.right.clone(),
                },
                BinOp::Ge(_) => RequirementKind::GreaterEqual {
                    left: *bin.left.clone(),
                    right: *bin.right.clone(),
                },
                BinOp::Eq(_) => RequirementKind::Equal {
                    left: *bin.left.clone(),
                    right: *bin.right.clone(),
                },
                BinOp::Ne(_) => RequirementKind::NotEqual {
                    left: *bin.left.clone(),
                    right: *bin.right.clone(),
                },
                _ => {
                    return Err(syn::Error::new(
                        bin.op.span(),
                        "unsupported operator in require!() — supports <=, >=, ==, !=",
                    ));
                }
            };
            Ok(Requirement { kind })
        }
        // Check for method call: `set.contains(element)`
        Expr::MethodCall(mc) => {
            if mc.method == "contains" {
                let set = expr_to_ident_string(&mc.receiver)?;
                let element = mc
                    .args
                    .first()
                    .ok_or_else(|| {
                        syn::Error::new(mc.method.span(), "contains() requires one argument")
                    })
                    .and_then(|arg| expr_to_ident_string(arg))?;
                Ok(Requirement {
                    kind: RequirementKind::Membership { set, element },
                })
            } else {
                Err(syn::Error::new(
                    mc.method.span(),
                    "unsupported method call in require!() — supports .contains()",
                ))
            }
        }
        _ => Err(syn::Error::new(
            expr.span(),
            "require!() argument must be a binary comparison or .contains() call",
        )),
    }
}
