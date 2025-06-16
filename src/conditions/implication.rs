use std::sync::Arc;

use egg::{Analysis, Applier, Language, Pattern, PatternAst, Rewrite, Var};

use crate::{apply_pat, enumo::lookup_pattern, halide::Pred, SynthAnalysis, SynthLanguage};

use super::assumption::Assumption;


/// Represents a logical implication between two assumptions, e.g.,
/// `(> x 0) -> (!= x 0)`.
///
/// Each assumption is represented as a pattern over the language `L`.
/// Implications are primarily used to propagate a root condition,
/// which is seeded into an empty e-graph to prune derivable rewrites.
#[derive(Clone, PartialEq, Debug)]
pub struct Implication<L: SynthLanguage> {
    pub name: Arc<str>,
    pub lhs: Assumption<L>,
    pub rhs: Assumption<L>,
}

impl<L: SynthLanguage> Implication<L> {
    /// Returns a human-readable name for the implication.
    #[inline]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the left-hand side pattern of the implication.
    #[inline]
    pub fn lhs(&self) -> Pattern<L> {
        self.lhs.clone().into()
    }

    /// Returns a reference to the right-hand side pattern of the implication.
    #[inline]
    pub fn rhs(&self) -> Pattern<L> {
        self.rhs.clone().into()
    }
    

    /// Whether the implication is valid, i.e., whether the left-hand side implies the right-hand side.
    pub fn is_valid(&self) -> bool {
        matches!(L::validate_implication(self.clone()), ImplicationValidationResult::NonTrivialValid)
    }

    /// Converts the implication into a rewrite rule.
    ///
    /// Even though the type of the rewrite is `Rewrite<L, SynthAnalysis>`,
    /// these are **not** traditional rewrites that represent equalities
    /// assumption pattern is added to the e-graph as well.
    ///
    /// ```
    /// use ruler::conditions::Implication;
    /// use ruler::halide::Pred;
    /// use ruler::language::{SynthLanguage, SynthAnalysis};
    /// use egg::{Rewrite, RecExpr};
    ///
    /// use std::str::FromStr;
    ///
    /// let imp: Implication<Pred> = Implication::new(
    ///    "(> x 0) -> (!= x 0)",
    ///   "(> x 0)".parse().unwrap(),
    ///   "(!= x 0)".parse().unwrap(),
    /// );
    ///
    /// let rewrite: Rewrite<Pred, SynthAnalysis> = imp.rewrite();
    ///
    /// let egraph = &mut egg::EGraph::<Pred, SynthAnalysis>::default();
    /// let assume_p_expr: RecExpr<Pred> = Pred::make_assumption(&"(> x 0)".parse().unwrap()).to_string().parse().unwrap();
    /// egraph.add_expr(assume_p_expr.to_string().parse().unwrap());
    ///
    ///
    /// let runner = egg::Runner::default().with_egraph(egraph.clone());
    /// runner.run(&[rewrite]);
    ///
    /// let result = runner.egraph;
    /// let assume_q: egg::RecExpr<Pred> = Pred::make_assumption(&"q".parse().unwrap()).to_string().parse().unwrap();
    /// let assume_q_id = result.lookup_expr(&assume_q);
    /// ```
    pub fn rewrite(&self) -> Rewrite<L, SynthAnalysis> {
        assert!(self.is_valid(), "Implication is not valid: {}", self.name());
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
        let lhs = self.implication.lhs();
        let rhs = self.implication.rhs();

        // First, search for the left-hand side pattern in the egraph.
        // If it's not there, something terrible happened.
        assert!(lookup_pattern(&lhs, egraph, subst), "For implication {}, could not find {}", self.implication.name(), lhs);

        // TODO: if this is expensive, we might be able to comment this out?
        if lookup_pattern(&rhs, egraph, subst) {
            // we already have the condition in the egraph, so no need to add it.
            return vec![];
        }

        let new_id = apply_pat(
            rhs.ast.as_ref().iter().as_slice(),
            egraph,
            subst,
        );

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
// For example, given the pattern (istrue (== ?a ?b)), this applier
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

pub fn merge_eqs() -> Rewrite<Pred, SynthAnalysis> {
    let searcher: Pattern<Pred> = "(istrue (== ?a ?b))".parse().unwrap();
    // union ?a and ?b.
    let applier = EqApplier {
        a: "?a".parse().unwrap(),
        b: "?b".parse().unwrap(),
    };

    Rewrite::new("istrue-eqs", searcher, applier).unwrap()
}

pub mod tests {
    use egg::{EGraph, Runner};

    use crate::{enumo::egg_to_serialized_egraph, ImplicationSwitch};

    use super::*;
    #[test]
    fn merge_eqs_merges() {
        let rule: ImplicationSwitch<Pred> = ImplicationSwitch {
            parent_cond: "(!= ?x 0)".parse().unwrap(),
            my_cond: "(== (/ ?x ?x) 1)".parse().unwrap(),
        };

        let egraph = &mut EGraph::<Pred, SynthAnalysis>::default();

        egraph.add_expr(&"(istrue (!= x 0))".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[rule.rewrite(), merge_eqs()]);

        let egraph = runner.egraph.clone();

        assert!(egraph
            .lookup_expr(&"(istrue (== (/ x x) 1))".parse().unwrap())
            .is_some());

        assert_eq!(
            egraph.lookup_expr(&"(/ x x)".parse().unwrap()),
            egraph.lookup_expr(&"1".parse().unwrap())
        );
    }
}