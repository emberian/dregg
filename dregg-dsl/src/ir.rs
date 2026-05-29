//! Intermediate representation for dregg constraints.
//!
//! The IR captures the semantic content of a constraint function:
//! its name, typed parameters, and a list of statements. Each backend
//! (Rust evaluator, AIR descriptor, Datalog, Kimchi) consumes this IR to emit
//! its target code.

/// A single constraint function parsed from a `#[dregg_caveat]` or `#[dregg_effect]` annotation.
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
    /// A 2D array of bytes: `[[u8; 32]; N]`. Used as the siblings array for
    /// Merkle membership proofs. The `u32` is the outer length (`N`).
    ByteMatrix32(u32),
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
    /// `set.contains(element)` — set membership against an in-memory set.
    Membership { set: String, element: String },
    /// `in_range!(value, N)` — i.e. `value < 2^N`, proven via bit decomp.
    BitRange { value: syn::Expr, bits: u32 },
    /// `merkle_member!(root, leaf, position, siblings, depth = N)` — Merkle
    /// inclusion proof. `root` and `leaf` are 32-byte digests, `position` is
    /// a `u64` index, and `siblings` is a `&[[u8; 32]; N]` array of length
    /// `depth`. The proof uses Poseidon2 `hash_2_to_1` as the underlying
    /// compression function, with sibling ordering driven by the bits of
    /// `position` (bit 0 = leaf level, bit `depth-1` = root level).
    MerkleAtPosition {
        root: syn::Expr,
        leaf: syn::Expr,
        position: syn::Expr,
        siblings: syn::Expr,
        depth: u32,
    },
    /// `poseidon2_assert!(output, a, b, ...)` — assert
    /// `output == poseidon2_hash([a, b, ...])` where each input and the
    /// output is a 32-byte digest. Used for state commitments, effects
    /// hashes, capability roots, swiss-table root binding.
    Poseidon2Hash {
        inputs: Vec<syn::Expr>,
        output: syn::Expr,
    },
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
            RequirementKind::BitRange { .. } => "in_range",
            RequirementKind::MerkleAtPosition { .. } => "merkle_member",
            RequirementKind::Poseidon2Hash { .. } => "poseidon2",
        }
    }
}
