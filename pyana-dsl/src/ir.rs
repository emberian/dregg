/// Intermediate representation for pyana constraints.
///
/// The IR captures the semantic content of a constraint function:
/// its name, typed parameters, and a list of requirements. Each backend
/// (Rust evaluator, AIR descriptor, Datalog) consumes this IR to emit
/// its target code.

/// A single constraint function parsed from a `#[pyana_caveat]` annotation.
pub struct ConstraintIr {
    pub name: syn::Ident,
    pub params: Vec<Param>,
    pub requirements: Vec<Requirement>,
}

/// A typed parameter to a constraint function.
pub struct Param {
    pub name: syn::Ident,
    pub ty: ParamType,
}

/// The restricted type system for Phase 1.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamType {
    U64,
    ByteArray32,
}

/// A single `require!(expr)` statement, classified by shape.
pub struct Requirement {
    pub kind: RequirementKind,
}

/// The classification of a requirement expression.
#[derive(Clone)]
pub enum RequirementKind {
    /// `a <= b`
    LessEqual { left: syn::Expr, right: syn::Expr },
    /// `a >= b`
    GreaterEqual { left: syn::Expr, right: syn::Expr },
    /// `a == b`
    Equal { left: syn::Expr, right: syn::Expr },
    /// `a != b`
    NotEqual { left: syn::Expr, right: syn::Expr },
}

impl RequirementKind {
    /// Human-readable operator for error messages.
    pub fn op_str(&self) -> &'static str {
        match self {
            RequirementKind::LessEqual { .. } => "<=",
            RequirementKind::GreaterEqual { .. } => ">=",
            RequirementKind::Equal { .. } => "==",
            RequirementKind::NotEqual { .. } => "!=",
        }
    }
}
