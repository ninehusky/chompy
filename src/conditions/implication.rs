use std::{str::FromStr, sync::Arc};

use egg::{Analysis, Applier, Language, Pattern, PatternAst, Rewrite, Var};

use crate::{
    apply_pat,
    enumo::{lookup_pattern, Sexp},
    halide::Pred,
    SynthAnalysis, SynthLanguage,
};

use super::assumption::Assumption;

/// Represents a logical implication between two assumptions.
/// Implications can either be concrete, e.g.,
/// `(> x 0) -> (!= x 0)`, or symbolic, e.g.,
/// `(> ?x 0) -> (!= ?x 0)`. It's up to the users to make sure that
/// the left and right sides of the implications are both either concrete or symbolic;
/// combining the two results in undefined behavior.
///
/// Each assumption is represented as a pattern over the language `L`.
/// Implications are primarily used to propagate a root condition,
/// which is seeded into an empty e-graph to prune derivable rewrites.
#[derive(Clone, PartialEq, Debug)]
pub struct Implication<L: SynthLanguage> {
    name: Arc<str>,
    lhs: Assumption<L>,
    rhs: Assumption<L>,
}

impl<L: SynthLanguage> Implication<L> {
    /// Creates a new implication from the given name, left-hand side, and right-hand side assumptions.
    ///
    /// # Errors
    /// Returns an error if the right-hand side contains variables not present in the left-hand side.
    pub fn new(name: Arc<str>, lhs: Assumption<L>, rhs: Assumption<L>) -> Result<Self, String> {
        let mut map = Default::default();
        let lhs_pat: Pattern<L> = L::generalize(&lhs.clone().into(), &mut map);
        let rhs_pat: Pattern<L> = L::generalize(&rhs.clone().into(), &mut map);

        let lhs_vars = lhs_pat.vars();
        let rhs_vars = rhs_pat.vars();

        if rhs_vars.iter().any(|v| !lhs_vars.contains(v)) {
            return Err(format!(
                "Right-hand side of implication '{}' contains variables not present in the left-hand side: {:?}",
                name, rhs_vars
            ));
        }

        Ok(Implication { name, lhs, rhs })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn lhs(&self) -> Assumption<L> {
        self.lhs.clone()
    }

    pub fn rhs(&self) -> Assumption<L> {
        self.rhs.clone()
    }
    /// Whether the implication is valid, i.e., whether the left-hand side implies the right-hand side.
    pub fn is_valid(&self) -> bool {
        matches!(
            L::validate_implication(self.clone()),
            ImplicationValidationResult::NonTrivialValid
        )
    }

    /// Returns the score of the implication.
    /// By default, the score is 2 + the sum of the sizes of the left-hand side and right-hand side assumptions,
    /// with a slight penalty for literals (numbers). See below for why we add the 2.
    /// ```
    /// use ruler::conditions::implication::Implication;
    /// use ruler::conditions::assumption::Assumption;
    /// use ruler::halide::Pred;
    /// use ruler::language::{SynthLanguage, SynthAnalysis};
    /// use std::str::FromStr;
    ///
    ///
    /// // (assume (> x 0)): 3 atoms, 1 literal: 3 + 1.1 = 4.1
    /// let lhs: Assumption<Pred> = Assumption::new("(> x 0)".to_string()).unwrap();
    /// // (assume (== (/ x x) 1)): 5 atoms, 1 literal: 5 + 1.1 = 6.1
    /// let rhs: Assumption<Pred> = Assumption::new("(== (/ x x) 1)".to_string()).unwrap();
    /// let imp: Implication<Pred> = Implication::new("my imp!".into(), lhs, rhs).unwrap();
    ///
    /// assert_eq!(imp.score(), [10.2]);
    /// ```
    // TODO: let's make the score prioritize implications with more variables.
    pub fn score(&self) -> [f64; 1] {
        fn size(sexp: &Sexp) -> f64 {
            match sexp {
                Sexp::Atom(a) => {
                    if let Ok(_) = a.parse::<i64>() {
                        // slight penalty for literals.
                        return 1.1;
                    } else {
                        return 1.0;
                    }
                }
                Sexp::List(l) => l.iter().map(size).sum(),
            }
        }

        let lhs = Sexp::from_str(&self.lhs().to_string()).unwrap();
        let rhs = Sexp::from_str(&self.rhs().to_string()).unwrap();

        [size(&lhs) + size(&rhs)]
    }

    /// Converts the implication into a rewrite rule.
    ///
    /// Even though the type of the rewrite is `Rewrite<L, SynthAnalysis>`,
    /// these are **not** traditional rewrites that represent equalities.
    ///
    /// ```
    /// use ruler::conditions::implication::Implication;
    /// use ruler::conditions::assumption::Assumption;
    /// use ruler::halide::Pred;
    /// use ruler::language::{SynthLanguage, SynthAnalysis};
    /// use egg::{Rewrite, RecExpr};
    ///
    /// use std::str::FromStr;
    ///
    /// let imp: Implication<Pred> = Implication::new(
    ///   "(> x 0) -> (!= x 0)".into(),
    ///   Assumption::new("(> x 0)".to_string()).unwrap(),
    ///   Assumption::new("(!= x 0)".to_string()).unwrap(),
    /// ).unwrap();
    ///
    /// let rewrite: Rewrite<Pred, SynthAnalysis> = imp.rewrite();
    ///
    /// let mut egraph = egg::EGraph::<Pred, SynthAnalysis>::default();
    /// imp.lhs().insert_into_egraph(&mut egraph);
    ///
    ///
    /// let runner = egg::Runner::default().with_egraph(egraph.clone()).run(&[rewrite]);
    ///
    /// let result = runner.egraph;
    /// // Let's check if the right-hand assumption is present in the egraph.
    /// assert!(result.lookup_expr(&imp.rhs().clone().into()).is_some());
    /// // Observe also that the left-hand and right-hand assumptions are not equal.
    /// assert_ne!(result.lookup_expr(&imp.lhs().clone().into()),
    ///            result.lookup_expr(&imp.rhs().clone().into()));
    /// ```
    pub fn rewrite(&self) -> Rewrite<L, SynthAnalysis> {
        assert!(self.is_valid(), "Implication is not valid: {}", self.name);
        Rewrite::new(
            format!("impl: {}", self.name),
            Pattern::<L>::from(self.lhs.clone()),
            ImplicationApplier {
                implication: self.clone(),
            },
        )
        .unwrap()
    }
}

struct ImplicationApplier<L: SynthLanguage> {
    implication: Implication<L>,
}

impl<L> Applier<L, SynthAnalysis> for ImplicationApplier<L>
where
    L: SynthLanguage,
{
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<L, SynthAnalysis>,
        _eclass: egg::Id,
        subst: &egg::Subst,
        _searcher_ast: Option<&PatternAst<L>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let lhs: Pattern<L> = self.implication.lhs.clone().into();
        let rhs: Pattern<L> = self.implication.rhs.clone().into();

        // First, search for the left-hand side pattern in the egraph.
        // If it's not there, something terrible happened.
        assert!(
            lookup_pattern(&lhs, egraph, subst),
            "For implication {}, could not find {}",
            self.implication.name,
            lhs
        );

        // TODO: if this is expensive, we might be able to comment this out?
        if lookup_pattern(&rhs, egraph, subst) {
            // we already have the condition in the egraph, so no need to add it.
            return vec![];
        }

        let new_id = apply_pat(rhs.ast.as_ref().iter().as_slice(), egraph, subst);

        vec![new_id]
    }
}

/// Result of validating an implication.
#[derive(Debug, PartialEq, Eq)]
pub enum ImplicationValidationResult {
    /// The left-hand side of the implication is false, meaning the implication is trivially true.
    LhsFalse,
    /// The right-hand side of the implication is true, meaning the implication is trivially true.
    RhsTrue,
    /// The implication is useful and valid.
    NonTrivialValid,
    /// The implication is invalid.
    Invalid,
    /// The validity of the implication is unknown.
    Unknown,
}

// A helper applier that unions two terms in the e-graph, given
// an assumption node which indicates their equality.
// For example, given the pattern (assume (== ?a ?b)), this applier
// will union ?a and ?b in the e-graph.
pub(crate) struct EqApplier {
    pub(crate) a: Var,
    pub(crate) b: Var,
}

impl<L: Language, N: Analysis<L>> Applier<L, N> for EqApplier {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<L, N>,
        _eclass: egg::Id,
        subst: &egg::Subst,
        _searcher_ast: Option<&egg::PatternAst<L>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst.get(self.a).unwrap();
        let b = subst.get(self.b).unwrap();
        if egraph.union(*a, *b) {
            vec![*a, *b]
        } else {
            vec![]
        }
    }
}

pub fn merge_eqs<L: SynthLanguage>() -> Rewrite<L, SynthAnalysis> {
    let searcher: Pattern<L> = "(assume (== ?a ?b))".parse().unwrap();
    // union ?a and ?b.
    let applier = EqApplier {
        a: "?a".parse().unwrap(),
        b: "?b".parse().unwrap(),
    };

    Rewrite::new("assume-eqs", searcher, applier).unwrap()
}

#[allow(unused_imports)]
mod implication_tests {
    use crate::conditions::assumption::Assumption;
    use crate::conditions::implication::{Implication, ImplicationValidationResult};
    use crate::halide::Pred;
    use crate::SynthLanguage;

    #[test]
    fn implication_fields_ok() {
        let lhs: Assumption<Pred> = Assumption::new("(> x 0)".to_string()).unwrap();
        let rhs: Assumption<Pred> = Assumption::new("(!= x 0)".to_string()).unwrap();

        let implication = Implication::new("imp1".into(), lhs.clone(), rhs.clone()).unwrap();

        assert_eq!(implication.name(), "imp1");
        assert_eq!(implication.lhs(), lhs);
        assert_eq!(implication.rhs(), rhs);
    }

    #[test]
    fn implication_fails_with_unbound_vars() {
        let lhs: Assumption<Pred> = Assumption::new("(> x 0)".to_string()).unwrap();
        let rhs: Assumption<Pred> = Assumption::new("(!= y 0)".to_string()).unwrap();

        let result = Implication::new("imp2".into(), lhs, rhs);

        assert!(
            result.is_err(),
            "Expected error for unbound variable in RHS"
        );
    }

    #[test]
    fn implication_rewrite_ok() {
        let lhs: Assumption<Pred> = Assumption::new("(> x 0)".to_string()).unwrap();
        let rhs: Assumption<Pred> = Assumption::new("(!= x 0)".to_string()).unwrap();

        let implication = Implication::new("imp1".into(), lhs.clone(), rhs.clone()).unwrap();

        let rewrite = implication.rewrite();

        let mut egraph = egg::EGraph::<Pred, crate::SynthAnalysis>::default();

        // Insert the left-hand side assumption into the egraph.
        implication.lhs().insert_into_egraph(&mut egraph);

        // (assume (> x 0)) should be in the egraph.
        assert_eq!(egraph.number_of_classes(), 4);
        assert!(egraph.lookup_expr(&lhs.clone().into()).is_some());

        let runner = egg::Runner::default()
            .with_egraph(egraph.clone())
            .run(&[rewrite]);

        let result = runner.egraph;

        // The right-hand side assumption should now be in the egraph.
        assert_eq!(result.number_of_classes(), 6);
        assert!(result.lookup_expr(&rhs.clone().into()).is_some());

        assert_ne!(
            result.lookup_expr(&lhs.into()),
            result.lookup_expr(&rhs.into()),
            "Left-hand and right-hand assumptions should not be equal"
        );
    }

    #[test]
    fn implication_score_correct() {
        // (assume (> x 0)): 3 atoms, 1 literal: 3 + 1.1 = 4.1
        let lhs: Assumption<Pred> = Assumption::new("(> x 0)".to_string()).unwrap();
        // (assume (== (/ x x) 1)): 5 atoms, 1 literal: 5 + 1.1 = 6.1
        let rhs: Assumption<Pred> = Assumption::new("(== (/ x x) 1)".to_string()).unwrap();
        let imp: Implication<Pred> = Implication::new("my imp!".into(), lhs, rhs).unwrap();

        assert_eq!(imp.score(), [10.2]);
    }

    // Halide-specific tests for implications.
    #[test]
    fn implication_validate_valid() {
        let lhs: Assumption<Pred> = Assumption::new("(> x 0)".to_string()).unwrap();
        let rhs: Assumption<Pred> = Assumption::new("(!= x 0)".to_string()).unwrap();

        let implication = Implication::new("imp1".into(), lhs, rhs).unwrap();

        assert_eq!(
            Pred::validate_implication(implication.clone()),
            ImplicationValidationResult::NonTrivialValid
        );
        assert!(implication.is_valid());
    }

    #[test]
    fn implication_validate_lhs_false() {
        let lhs: Assumption<Pred> = Assumption::new("(!= x x)".to_string()).unwrap();
        let rhs: Assumption<Pred> = Assumption::new("(!= x 0)".to_string()).unwrap();

        let implication = Implication::new("imp2".into(), lhs, rhs).unwrap();

        assert_eq!(
            Pred::validate_implication(implication.clone()),
            ImplicationValidationResult::LhsFalse
        );
        assert!(!implication.is_valid());
    }

    #[test]
    fn implication_validate_rhs_true() {
        let lhs: Assumption<Pred> = Assumption::new("(> x 0)".to_string()).unwrap();
        let rhs: Assumption<Pred> = Assumption::new("(== x x)".to_string()).unwrap();

        let implication = Implication::new("imp3".into(), lhs, rhs).unwrap();

        assert_eq!(
            Pred::validate_implication(implication.clone()),
            ImplicationValidationResult::RhsTrue
        );
        assert!(!implication.is_valid());
    }

    #[test]
    fn implication_validate_invalid() {
        let lhs: Assumption<Pred> = Assumption::new("(> x 0)".to_string()).unwrap();
        let rhs: Assumption<Pred> = Assumption::new("(< x 0)".to_string()).unwrap();

        let implication = Implication::new("imp4".into(), lhs, rhs).unwrap();

        assert_eq!(
            Pred::validate_implication(implication.clone()),
            ImplicationValidationResult::Invalid
        );
        assert!(!implication.is_valid());
    }
}

#[allow(unused_imports)]
mod eq_tests {
    use crate::{enumo::egg_to_serialized_egraph, ImplicationSwitch};
    use egg::{EGraph, Runner};

    use super::*;
    #[test]
    fn merge_eqs_merges() {
        let rule: ImplicationSwitch<Pred> = ImplicationSwitch {
            parent_cond: "(!= ?x 0)".parse().unwrap(),
            my_cond: "(== (/ ?x ?x) 1)".parse().unwrap(),
        };

        let egraph = &mut EGraph::<Pred, SynthAnalysis>::default();

        egraph.add_expr(&"(assume (!= x 0))".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[rule.rewrite(), merge_eqs()]);

        let egraph = runner.egraph.clone();

        assert!(egraph
            .lookup_expr(&"(assume (== (/ x x) 1))".parse().unwrap())
            .is_some());

        assert_eq!(
            egraph.lookup_expr(&"(/ x x)".parse().unwrap()),
            egraph.lookup_expr(&"1".parse().unwrap())
        );
    }
}
