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
        let lhs_pat: Pattern<L> = lhs.clone().into();
        let rhs_pat: Pattern<L> = rhs.clone().into();

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
        matches!(L::validate_implication(self.clone()), ImplicationValidationResult::NonTrivialValid)
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
        assert!(lookup_pattern(&lhs, egraph, subst), "For implication {}, could not find {}", self.implication.name, lhs);

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