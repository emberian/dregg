use pyana_dsl::pyana_caveat;

#[pyana_caveat]
fn not_after(token_expiry: u64, current_time: u64) {
    require!(current_time <= token_expiry);
}

#[pyana_caveat]
fn minimum_balance(balance: u64, threshold: u64) {
    require!(balance >= threshold);
}

#[pyana_caveat]
fn exact_match(expected: u64, actual: u64) {
    require!(expected == actual);
}

#[pyana_caveat]
fn different_parties(sender: u64, receiver: u64) {
    require!(sender != receiver);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_not_after_evaluator_pass() {
        assert!(not_after_check(100, 50).is_ok());
    }

    #[test]
    fn test_not_after_evaluator_boundary() {
        assert!(not_after_check(100, 100).is_ok());
    }

    #[test]
    fn test_not_after_evaluator_fail() {
        assert!(not_after_check(50, 100).is_err());
    }

    #[test]
    fn test_not_after_air_descriptor() {
        let air = not_after_air_constraints();
        assert_eq!(air.name, "not_after");
        assert!(air.width > 0);
        // 2 params + 2 auxiliary (diff + bit) = 4
        assert_eq!(air.width, 4);
        assert_eq!(air.constraints.len(), 1);
        assert_eq!(air.public_inputs.len(), 2);
    }

    #[test]
    fn test_not_after_datalog() {
        let rule = not_after_datalog();
        assert!(rule.contains("not_after_satisfied"));
        assert!(rule.contains("<="));
    }

    #[test]
    fn test_minimum_balance_pass() {
        assert!(minimum_balance_check(100, 50).is_ok());
        assert!(minimum_balance_check(50, 50).is_ok());
    }

    #[test]
    fn test_minimum_balance_fail() {
        assert!(minimum_balance_check(49, 50).is_err());
    }

    #[test]
    fn test_exact_match_pass() {
        assert!(exact_match_check(42, 42).is_ok());
    }

    #[test]
    fn test_exact_match_fail() {
        assert!(exact_match_check(42, 43).is_err());
    }

    #[test]
    fn test_different_parties_pass() {
        assert!(different_parties_check(1, 2).is_ok());
    }

    #[test]
    fn test_different_parties_fail() {
        assert!(different_parties_check(1, 1).is_err());
    }

    #[test]
    fn test_exact_match_air_no_extra_cols() {
        let air = exact_match_air_constraints();
        // equality needs no auxiliary columns: just 2 param columns
        assert_eq!(air.width, 2);
    }

    #[test]
    fn test_different_parties_air_inverse_col() {
        let air = different_parties_air_constraints();
        // 2 params + 1 inverse witness = 3
        assert_eq!(air.width, 3);
    }
}
