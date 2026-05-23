/// Parser: converts a syn-parsed function into our constraint IR.
///
/// Expects:
/// - Function parameters with types `u64` or `[u8; 32]`
/// - Body containing `require!(expr)` macro invocations
/// - Each `require!` argument must be a binary comparison

use proc_macro2::Span;
use syn::{spanned::Spanned, BinOp, Expr, FnArg, ItemFn, Pat, Stmt, Type};

use crate::ir::{ConstraintIr, Param, ParamType, Requirement, RequirementKind};

pub fn parse_caveat(func: &ItemFn) -> Result<ConstraintIr, syn::Error> {
    let name = func.sig.ident.clone();
    let params = parse_params(func)?;
    let requirements = parse_body(func)?;

    if requirements.is_empty() {
        return Err(syn::Error::new(
            func.block.span(),
            "pyana_caveat function must contain at least one require!() statement",
        ));
    }

    Ok(ConstraintIr {
        name,
        params,
        requirements,
    })
}

fn parse_params(func: &ItemFn) -> Result<Vec<Param>, syn::Error> {
    let mut params = Vec::new();
    for arg in &func.sig.inputs {
        match arg {
            FnArg::Typed(pat_type) => {
                let ident = match pat_type.pat.as_ref() {
                    Pat::Ident(pi) => pi.ident.clone(),
                    _ => {
                        return Err(syn::Error::new(
                            pat_type.pat.span(),
                            "pyana_caveat parameters must be simple identifiers",
                        ));
                    }
                };
                let ty = parse_type(&pat_type.ty)?;
                params.push(Param { name: ident, ty });
            }
            FnArg::Receiver(_) => {
                return Err(syn::Error::new(
                    arg.span(),
                    "pyana_caveat functions cannot have self parameters",
                ));
            }
        }
    }
    Ok(params)
}

fn parse_type(ty: &Type) -> Result<ParamType, syn::Error> {
    match ty {
        Type::Path(tp) => {
            let seg = tp
                .path
                .segments
                .last()
                .ok_or_else(|| syn::Error::new(tp.path.span(), "empty type path"))?;
            if seg.ident == "u64" {
                Ok(ParamType::U64)
            } else {
                Err(syn::Error::new(
                    seg.ident.span(),
                    format!(
                        "unsupported type `{}` in pyana_caveat (Phase 1 supports u64 and [u8; 32])",
                        seg.ident
                    ),
                ))
            }
        }
        Type::Array(_) => {
            // Accept [u8; 32] — we don't deeply validate the element type/length here
            // since that will be caught at use-site anyway.
            Ok(ParamType::ByteArray32)
        }
        _ => Err(syn::Error::new(
            ty.span(),
            "unsupported type in pyana_caveat (Phase 1 supports u64 and [u8; 32])",
        )),
    }
}

fn parse_body(func: &ItemFn) -> Result<Vec<Requirement>, syn::Error> {
    let mut requirements = Vec::new();

    for stmt in &func.block.stmts {
        match stmt {
            Stmt::Macro(sm) => {
                if is_require_macro(&sm.mac) {
                    let req = parse_require_macro(&sm.mac)?;
                    requirements.push(req);
                } else {
                    return Err(syn::Error::new(
                        sm.mac.path.span(),
                        "only require!() macros are supported in pyana_caveat bodies (Phase 1)",
                    ));
                }
            }
            Stmt::Expr(expr, _semi) => {
                if let Some(req) = try_parse_expr_as_require(expr)? {
                    requirements.push(req);
                } else {
                    return Err(syn::Error::new(
                        expr.span(),
                        "only require!() statements are supported in pyana_caveat bodies (Phase 1)",
                    ));
                }
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "only require!() statements are supported in pyana_caveat bodies (Phase 1)",
                ));
            }
        }
    }

    Ok(requirements)
}

fn is_require_macro(mac: &syn::Macro) -> bool {
    mac.path
        .segments
        .last()
        .is_some_and(|seg| seg.ident == "require")
}

fn try_parse_expr_as_require(expr: &Expr) -> Result<Option<Requirement>, syn::Error> {
    if let Expr::Macro(em) = expr {
        if is_require_macro(&em.mac) {
            return Ok(Some(parse_require_macro(&em.mac)?));
        }
    }
    Ok(None)
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
                        "unsupported operator in require!() — Phase 1 supports <=, >=, ==, !=",
                    ));
                }
            };
            Ok(Requirement { kind })
        }
        _ => Err(syn::Error::new(
            expr.span(),
            "require!() argument must be a binary comparison (a <= b, a >= b, a == b, a != b)",
        )),
    }
}
