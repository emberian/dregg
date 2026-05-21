//! Core data types for the derivation trace format.

use serde::{Deserialize, Serialize};

/// A symbol is a 32-byte field element or hash, used as predicate/constant identifiers.
pub type Symbol = [u8; 32];

/// A variable is identified by a numeric index.
pub type Variable = u32;

/// A term in the Datalog language: a constant, integer, or variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Term {
    /// A symbolic constant (predicate name, string hash, etc.)
    Const(Symbol),
    /// An integer literal (timestamps, counts, etc.)
    Int(i64),
    /// A variable reference.
    Var(Variable),
}

/// An atom (predicate application) in the Datalog language.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Atom {
    /// The predicate symbol.
    pub predicate: Symbol,
    /// The terms (arguments). Maximum 3 terms per atom.
    pub terms: Vec<Term>,
}

/// A constraint check attached to a rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Check {
    /// `lhs < rhs`
    LessThan(Term, Term),
    /// `lhs > rhs`
    GreaterThan(Term, Term),
    /// `lhs >= rhs`
    GreaterThanOrEqual(Term, Term),
    /// `lhs == rhs`
    Equal(Term, Term),
    /// `lhs` contains `rhs` (set membership / string containment).
    ///
    /// DEPRECATED for action checking — use `MemberOf` instead to avoid
    /// the substring vulnerability where e.g. `"threadwrite"` would match
    /// `"write"` via substring. Retained for backward compatibility with
    /// existing serialized traces and non-action use cases.
    Contains(Term, Term),
    /// `element` is a member of the action set.
    ///
    /// Semantics: the element (a BLAKE3 action hash stored as a 32-byte
    /// Const) must exactly match one of the `action_allowed` facts for the
    /// same resource. Unlike `Contains`, this does exact hash equality —
    /// no substring matching, no prefix/suffix collisions.
    ///
    /// In the local evaluator: implemented as equality check on the resolved
    /// action hash against each element in the action set body atom.
    /// In the ZK path: Merkle membership proof against the action set root.
    MemberOf(Term, Term),
}

/// A Datalog rule with head, body atoms, and constraint checks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Rule {
    /// Unique rule identifier.
    pub id: u32,
    /// The head atom (what is derived).
    pub head: Atom,
    /// Body atoms that must all be satisfied. Maximum 4 body atoms.
    pub body: Vec<Atom>,
    /// Constraint checks that must hold for the substitution.
    pub checks: Vec<Check>,
}

/// A ground fact (an atom with no variables).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Fact {
    /// The predicate symbol.
    pub predicate: Symbol,
    /// The ground terms (must not contain `Term::Var`).
    pub terms: Vec<Term>,
}

impl Fact {
    /// Create a new fact from a predicate and terms.
    pub fn new(predicate: Symbol, terms: Vec<Term>) -> Self {
        debug_assert!(
            terms.iter().all(|t| !matches!(t, Term::Var(_))),
            "Facts must be ground (no variables)"
        );
        Self { predicate, terms }
    }

    /// Convert this fact to an atom (for matching purposes).
    pub fn as_atom(&self) -> Atom {
        Atom {
            predicate: self.predicate,
            terms: self.terms.clone(),
        }
    }
}

/// A variable-to-term binding map.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Substitution {
    /// Ordered list of variable bindings.
    pub bindings: Vec<(Variable, Term)>,
}

impl Substitution {
    /// Create an empty substitution.
    pub fn empty() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    /// Look up a variable in this substitution.
    pub fn get(&self, var: Variable) -> Option<&Term> {
        self.bindings
            .iter()
            .find(|(v, _)| *v == var)
            .map(|(_, t)| t)
    }

    /// Extend this substitution with a new binding.
    /// Returns `None` if the variable is already bound to a different term.
    pub fn extend(&self, var: Variable, term: Term) -> Option<Self> {
        if let Some(existing) = self.get(var) {
            if *existing == term {
                Some(self.clone())
            } else {
                None
            }
        } else {
            let mut new = self.clone();
            new.bindings.push((var, term));
            Some(new)
        }
    }

    /// Apply this substitution to a term, resolving variables.
    pub fn apply_term(&self, term: &Term) -> Term {
        match term {
            Term::Var(v) => self.get(*v).cloned().unwrap_or(Term::Var(*v)),
            other => other.clone(),
        }
    }

    /// Apply this substitution to an atom.
    pub fn apply_atom(&self, atom: &Atom) -> Atom {
        Atom {
            predicate: atom.predicate,
            terms: atom.terms.iter().map(|t| self.apply_term(t)).collect(),
        }
    }

    /// Check if all variables in the given atom are bound.
    pub fn is_ground_for(&self, atom: &Atom) -> bool {
        atom.terms.iter().all(|t| match t {
            Term::Var(v) => self
                .get(*v)
                .is_some_and(|bound| !matches!(bound, Term::Var(_))),
            _ => true,
        })
    }
}

/// A single derivation step in a Datalog evaluation trace.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivationStep {
    /// The rule that was applied.
    pub rule_id: u32,
    /// The substitution used (variable bindings).
    pub substitution: Substitution,
    /// Indices into the fact set for each body atom that was matched.
    pub body_fact_indices: Vec<usize>,
    /// The new fact derived by this step.
    pub derived_fact: Fact,
}

/// The conclusion of an authorization evaluation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Conclusion {
    /// Authorization granted; includes the rule ID that allowed it.
    Allow { policy_rule_id: u32 },
    /// Authorization denied; no allow policy fired.
    Deny,
}

/// An authorization request to be evaluated against a policy.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthorizationRequest {
    /// The application identifier (if scoped to an app).
    pub app_id: Option<Symbol>,
    /// The service identifier (if scoped to a service).
    pub service: Option<Symbol>,
    /// The action being requested.
    pub action: Option<Symbol>,
    /// Feature flags / scopes.
    pub features: Vec<Symbol>,
    /// The user identifier.
    pub user_id: Option<Symbol>,
    /// Current timestamp (unix seconds).
    pub now: i64,
}

/// A complete derivation trace proving authorization.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthorizationTrace {
    /// The request that was evaluated.
    pub request: AuthorizationRequest,
    /// The derivation steps (in evaluation order).
    pub steps: Vec<DerivationStep>,
    /// The final conclusion.
    pub conclusion: Conclusion,
}

// -- Helper constructors for building symbols from strings --

/// Create a [`Symbol`] from a string by BLAKE3 hashing.
///
/// This produces a collision-resistant 32-byte identifier for any string,
/// regardless of length. Previously this function truncated at 32 bytes,
/// meaning two strings sharing the same 32-byte prefix would produce
/// identical symbols.
pub fn symbol_from_str(s: &str) -> Symbol {
    *blake3::hash(s.as_bytes()).as_bytes()
}

/// Create a [`Symbol`] from raw bytes by zero-padding or truncating to 32 bytes.
pub fn symbol_from_bytes(b: &[u8]) -> Symbol {
    let mut sym = [0u8; 32];
    let len = b.len().min(32);
    sym[..len].copy_from_slice(&b[..len]);
    sym
}
