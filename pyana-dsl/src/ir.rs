/// Intermediate representation for pyana constraints.
///
/// The IR captures the semantic content of a constraint function:
/// its name, typed parameters, and a list of statements. Each backend
/// (Rust evaluator, AIR descriptor, Datalog, Kimchi) consumes this IR to emit
/// its target code.

/// A single constraint function parsed from a `#[pyana_caveat]` or `#[pyana_effect]` annotation.
pub struct ConstraintIr {
    pub name: syn::Ident,
    pub params: Vec<Param>,
    /// The body statements (requirements, mutations, match arms).
    pub statements: Vec<Statement>,
    /// Whether this is an effect (has mutations) vs a pure caveat.
    pub is_effect: bool,
    /// Permission requirement (e.g., `requires = "Send"`).
    pub required_permission: Option<String>,
}

// Backwards compat: expose a `requirements` view for code that only needs requirements.
impl ConstraintIr {
    /// Extract all top-level requirements (flattening match arms).
    pub fn all_requirements(&self) -> Vec<&Requirement> {
        let mut out = Vec::new();
        for stmt in &self.statements {
            Self::collect_requirements(stmt, &mut out);
        }
        out
    }

    fn collect_requirements<'a>(stmt: &'a Statement, out: &mut Vec<&'a Requirement>) {
        match stmt {
            Statement::Require(req) => out.push(req),
            Statement::Mutate { .. } => {}
            Statement::Match { arms, .. } => {
                for arm in arms {
                    for s in &arm.body {
                        Self::collect_requirements(s, out);
                    }
                }
            }
        }
    }

    /// Extract all mutations (flattening match arms).
    pub fn all_mutations(&self) -> Vec<&Mutation> {
        let mut out = Vec::new();
        for stmt in &self.statements {
            Self::collect_mutations(stmt, &mut out);
        }
        out
    }

    fn collect_mutations<'a>(stmt: &'a Statement, out: &mut Vec<&'a Mutation>) {
        match stmt {
            Statement::Require(_) => {}
            Statement::Mutate(m) => out.push(m),
            Statement::Match { arms, .. } => {
                for arm in arms {
                    for s in &arm.body {
                        Self::collect_mutations(s, out);
                    }
                }
            }
        }
    }

    /// Get mutable parameters (those declared as `&mut T`).
    pub fn mutable_params(&self) -> Vec<&Param> {
        self.params.iter().filter(|p| p.mutable).collect()
    }
}

/// A typed parameter to a constraint function.
pub struct Param {
    pub name: syn::Ident,
    pub ty: ParamType,
    /// Whether this parameter is mutable (`&mut T`).
    pub mutable: bool,
}

/// The restricted type system.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamType {
    U64,
    ByteArray32,
    /// A set type (for membership checks).
    Set,
    /// A user-defined type (enums like Direction). Stored as the type path string.
    UserDefined(String),
}

/// A statement in the constraint body.
#[derive(Clone)]
pub enum Statement {
    /// A `require!(expr)` check.
    Require(Requirement),
    /// A mutation: `*target op= operand`.
    Mutate(Mutation),
    /// A match expression with arms.
    Match {
        discriminant: String,
        arms: Vec<MatchArm>,
    },
}

/// A single `require!(expr)` statement, classified by shape.
#[derive(Clone)]
pub struct Requirement {
    pub kind: RequirementKind,
}

/// A mutation operation.
#[derive(Clone)]
pub struct Mutation {
    pub target: String,
    pub op: MutateOp,
    pub operand: String,
}

/// Supported mutation operators.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MutateOp {
    SubAssign,
    AddAssign,
    Assign,
}

/// A match arm with a variant name and body statements.
#[derive(Clone)]
pub struct MatchArm {
    /// Short variant name (for Datalog, etc.)
    pub variant: String,
    /// Full pattern tokens (for Rust codegen)
    pub pattern_tokens: String,
    pub body: Vec<Statement>,
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
    /// `set.contains(element)` — set membership
    Membership { set: String, element: String },
}

impl RequirementKind {
    /// Human-readable operator for error messages.
    pub fn op_str(&self) -> &'static str {
        match self {
            RequirementKind::LessEqual { .. } => "<=",
            RequirementKind::GreaterEqual { .. } => ">=",
            RequirementKind::Equal { .. } => "==",
            RequirementKind::NotEqual { .. } => "!=",
            RequirementKind::Membership { .. } => "contains",
        }
    }
}
