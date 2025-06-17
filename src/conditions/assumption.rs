use egg::{Pattern, RecExpr};

use crate::SynthLanguage;

/// Represents an assumption over a language `L`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Assumption<L: SynthLanguage> {
    pat: String,
    _marker: std::marker::PhantomData<L>,
}

impl<L: SynthLanguage> Assumption<L> {
    /// Attempts to construct a new `Assumption` from the provided pattern string.
    ///
    /// # Arguments
    ///
    /// * `assumption` - A string representing the pattern to be wrapped as an assumption.
    ///
    /// # Returns
    ///
    /// * `Ok(Self)` if the pattern is a valid predicate and not already an assumption.
    /// * `Err(String)` if the pattern is invalid, not a predicate, or already an assumption.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The pattern cannot be parsed.
    /// - The pattern is already marked as an assumption.
    /// - The pattern is not recognized as a valid predicate in the language `L`.
    pub fn new(assumption: String) -> Result<Self, String> {
        let pat: Result<Pattern<L>, _> = assumption.parse();
        if pat.is_err() {
            return Err(format!(
                "Failed to parse assumption pattern: {}",
                assumption
            ));
        }
        let pat = pat.unwrap();
        if L::pattern_is_assumption(&pat) {
            return Err(format!("Pattern is already an assumption: {}", pat));
        } else if !L::pattern_is_predicate(&pat) {
            return Err(format!(
                "Pattern is not a valid predicate: {}",
                pat
            ));
        }

        Ok(Self {
            pat: assumption,
            _marker: std::marker::PhantomData,
        })
    }
}

impl<L: SynthLanguage> From<Assumption<L>> for Pattern<L> {
    fn from(assumption: Assumption<L>) -> Self {
        let string = format!("({} {})", L::assumption_label(), assumption.pat);

        string.parse().expect("Failed to parse assumption pattern")
    }
}

impl<L: SynthLanguage> From<Assumption<L>> for RecExpr<L> {
    fn from(assumption: Assumption<L>) -> Self {
        let string = format!("({} {})", L::assumption_label(), assumption.pat);

        string.parse().expect("Failed to parse assumption pattern")
    }
}

pub mod tests {
    use super::*;
    use crate::halide::Pred;
    use crate::SynthLanguage;

    #[test]
    fn test_assumption_creation() {
        let assumption_str = "(> x 0)".to_string();
        let assumption: Assumption<Pred> = Assumption::new(assumption_str).unwrap();
        let pattern: Pattern<Pred> = assumption.into();

        let expected_pattern: Pattern<Pred> = "(assume (> x 0))".parse().unwrap();

        assert_eq!(
            pattern, expected_pattern,
            "Assumption pattern does not match expected pattern"
        );
    }

    #[test]
    fn test_assumption_fail_unparsable() {
        let invalid_assumption_str = "(invalid x 0)".to_string();
        let result: Result<Assumption<Pred>, String> = Assumption::new(invalid_assumption_str);
        assert!(
            result.is_err(),
            "Expected error for invalid assumption pattern"
        );
    }

    #[test]
    fn test_assumption_fail_if_not_predicate() {
        let non_assumption_str = "(+ x 0)".to_string();
        let result: Result<Assumption<Pred>, String> = Assumption::new(non_assumption_str);
        assert!(result.is_err(), "Expected error for non-assumption pattern");
    }

    #[test]
    fn test_assumption_fail_if_already_assumption() {
        let predicate = "(> x 0)".to_string();
        let pattern: Pattern<Pred> = Assumption::<Pred>::new(predicate.clone()).unwrap().into();
        let result: Result<Assumption<Pred>, String> = Assumption::new(pattern.to_string());
        assert!(
            result.is_err(),
            "Expected error for pattern that is already an assumption"
        );
    }
}
