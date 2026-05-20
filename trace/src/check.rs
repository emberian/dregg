//! Constraint check evaluation, shared between the evaluator and verifier.

use crate::types::*;

/// Evaluate a single constraint check against a substitution.
pub fn eval_check(check: &Check, subst: &Substitution) -> bool {
    match check {
        Check::LessThan(lhs, rhs) => {
            let l = subst.apply_term(lhs);
            let r = subst.apply_term(rhs);
            matches!((&l, &r), (Term::Int(a), Term::Int(b)) if a < b)
        }
        Check::GreaterThan(lhs, rhs) => {
            let l = subst.apply_term(lhs);
            let r = subst.apply_term(rhs);
            matches!((&l, &r), (Term::Int(a), Term::Int(b)) if a > b)
        }
        Check::GreaterThanOrEqual(lhs, rhs) => {
            let l = subst.apply_term(lhs);
            let r = subst.apply_term(rhs);
            matches!((&l, &r), (Term::Int(a), Term::Int(b)) if a >= b)
        }
        Check::Equal(lhs, rhs) => {
            let l = subst.apply_term(lhs);
            let r = subst.apply_term(rhs);
            l == r
        }
        Check::Contains(collection, element) => {
            let col = subst.apply_term(collection);
            let elem = subst.apply_term(element);
            eval_contains(&col, &elem)
        }
        Check::MemberOf(element, set_element) => {
            let elem = subst.apply_term(element);
            let set_elem = subst.apply_term(set_element);
            eval_member_of(&elem, &set_elem)
        }
    }
}

/// Evaluate the "member_of" check.
///
/// Semantics: exact equality of two Const terms (both are BLAKE3 hashes).
/// Unlike `eval_contains`, this does NOT do substring matching — it requires
/// the element hash to exactly equal the set element hash.
///
/// This is the secure replacement for action checking: each action in the
/// allowed set is a separate fact, and the rule's body atom already unifies
/// the action_allowed fact. The MemberOf check simply confirms the request's
/// action hash matches the bound action hash (which is guaranteed by
/// unification, making this check a formality/belt-and-suspenders for the
/// ZK path where we need an explicit circuit constraint).
fn eval_member_of(element: &Term, set_element: &Term) -> bool {
    match (element, set_element) {
        (Term::Const(e), Term::Const(s)) => e == s,
        (Term::Int(e), Term::Int(s)) => e == s,
        _ => false,
    }
}

/// Evaluate the "contains" check.
///
/// Semantics: the collection symbol (interpreted as a UTF-8 string, zero-trimmed)
/// contains the element symbol as a substring. Equality also satisfies containment.
///
/// WARNING: This check is vulnerable to substring collisions. For action
/// checking, use `MemberOf` instead. This is retained for backward compatibility.
fn eval_contains(collection: &Term, element: &Term) -> bool {
    match (collection, element) {
        (Term::Const(c), Term::Const(e)) => {
            if c == e {
                return true;
            }
            let c_str = core::str::from_utf8(c)
                .unwrap_or("")
                .trim_end_matches('\0');
            let e_str = core::str::from_utf8(e)
                .unwrap_or("")
                .trim_end_matches('\0');
            if !e_str.is_empty() {
                c_str.contains(e_str)
            } else {
                false
            }
        }
        (Term::Int(c), Term::Int(e)) => c == e,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol_from_str;

    #[test]
    fn test_less_than_pass() {
        let check = Check::LessThan(Term::Var(0), Term::Int(1000));
        let subst = Substitution::empty().extend(0, Term::Int(500)).unwrap();
        assert!(eval_check(&check, &subst));
    }

    #[test]
    fn test_less_than_fail() {
        let check = Check::LessThan(Term::Var(0), Term::Int(1000));
        let subst = Substitution::empty().extend(0, Term::Int(2000)).unwrap();
        assert!(!eval_check(&check, &subst));
    }

    #[test]
    fn test_greater_than() {
        let check = Check::GreaterThan(Term::Int(100), Term::Var(0));
        let subst = Substitution::empty().extend(0, Term::Int(50)).unwrap();
        assert!(eval_check(&check, &subst));
    }

    #[test]
    fn test_equal_pass() {
        let check = Check::Equal(Term::Var(0), Term::Const(symbol_from_str("hello")));
        let subst = Substitution::empty()
            .extend(0, Term::Const(symbol_from_str("hello")))
            .unwrap();
        assert!(eval_check(&check, &subst));
    }

    #[test]
    fn test_equal_fail() {
        let check = Check::Equal(Term::Var(0), Term::Const(symbol_from_str("hello")));
        let subst = Substitution::empty()
            .extend(0, Term::Const(symbol_from_str("world")))
            .unwrap();
        assert!(!eval_check(&check, &subst));
    }

    #[test]
    fn test_contains_exact_match() {
        let check = Check::Contains(
            Term::Const(symbol_from_str("read")),
            Term::Const(symbol_from_str("read")),
        );
        assert!(eval_check(&check, &Substitution::empty()));
    }

    #[test]
    fn test_contains_substring() {
        let check = Check::Contains(
            Term::Const(symbol_from_str("read,write,delete")),
            Term::Const(symbol_from_str("write")),
        );
        assert!(eval_check(&check, &Substitution::empty()));
    }

    #[test]
    fn test_contains_miss() {
        let check = Check::Contains(
            Term::Const(symbol_from_str("read,write")),
            Term::Const(symbol_from_str("delete")),
        );
        assert!(!eval_check(&check, &Substitution::empty()));
    }

    #[test]
    fn test_contains_with_vars() {
        let check = Check::Contains(Term::Var(0), Term::Var(1));
        let subst = Substitution::empty()
            .extend(0, Term::Const(symbol_from_str("read,write")))
            .unwrap()
            .extend(1, Term::Const(symbol_from_str("read")))
            .unwrap();
        assert!(eval_check(&check, &subst));
    }

    // --- MemberOf tests ---

    #[test]
    fn test_member_of_exact_match() {
        // Same hash = member
        let hash = symbol_from_str("action_hash_abc");
        let check = Check::MemberOf(
            Term::Const(hash),
            Term::Const(hash),
        );
        assert!(eval_check(&check, &Substitution::empty()));
    }

    #[test]
    fn test_member_of_different_hashes() {
        // Different hashes = not a member
        let check = Check::MemberOf(
            Term::Const(symbol_from_str("hash_a")),
            Term::Const(symbol_from_str("hash_b")),
        );
        assert!(!eval_check(&check, &Substitution::empty()));
    }

    #[test]
    fn test_member_of_no_substring_vulnerability() {
        // The key security property: "threadwrite" hash != "write" hash
        // Even if the bytes of "write" appear as a substring somewhere,
        // the full 32-byte comparison will fail.
        let write_hash = symbol_from_str("write");
        let threadwrite_hash = symbol_from_str("threadwrite");
        let check = Check::MemberOf(
            Term::Const(threadwrite_hash),
            Term::Const(write_hash),
        );
        assert!(!eval_check(&check, &Substitution::empty()));
    }

    #[test]
    fn test_member_of_with_vars() {
        let action_hash = symbol_from_str("read_action_hash");
        let check = Check::MemberOf(Term::Var(0), Term::Var(1));
        let subst = Substitution::empty()
            .extend(0, Term::Const(action_hash))
            .unwrap()
            .extend(1, Term::Const(action_hash))
            .unwrap();
        assert!(eval_check(&check, &subst));
    }

    #[test]
    fn test_member_of_int_equality() {
        let check = Check::MemberOf(Term::Int(42), Term::Int(42));
        assert!(eval_check(&check, &Substitution::empty()));

        let check_fail = Check::MemberOf(Term::Int(42), Term::Int(43));
        assert!(!eval_check(&check_fail, &Substitution::empty()));
    }

    #[test]
    fn test_member_of_type_mismatch() {
        // Const vs Int = always false
        let check = Check::MemberOf(
            Term::Const(symbol_from_str("something")),
            Term::Int(42),
        );
        assert!(!eval_check(&check, &Substitution::empty()));
    }
}
