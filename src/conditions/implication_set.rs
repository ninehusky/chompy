use std::sync::Arc;

use egg::{EGraph, Pattern, RecExpr};
use egglog::EGraph as EgglogEGraph;

use crate::{conditions::manager::EGraphManager, enumo::Rule};
#[allow(unused_imports)]
use crate::{
    conditions::implication::{Implication, ImplicationValidationResult},
    enumo::Ruleset,
    IndexMap, SynthAnalysis, SynthLanguage,
};

const EGGLOG_REWRITE_RULESET_NAME: &'static str = "rewrites";
const EGGLOG_IMPLICATION_RULESET_NAME: &'static str = "path-finding";

/// A set of implications. Like a `Ruleset<L>`, but with implications instead of rewrites.
#[derive(Debug, Clone)]
pub struct ImplicationSet<L: SynthLanguage>(pub IndexMap<Arc<str>, Implication<L>>);

impl<L: SynthLanguage> Default for ImplicationSet<L> {
    fn default() -> Self {
        Self(IndexMap::default())
    }
}

impl<L: SynthLanguage> ImplicationSet<L> {
    pub fn new() -> Self {
        Self(IndexMap::default())
    }

    pub fn iter(&self) -> impl Iterator<Item = &Implication<L>> {
        self.0.values()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn contains(&self, val: &Implication<L>) -> bool {
        let key = val.name();
        self.0.contains_key(&Arc::<str>::from(key))
    }

    pub fn add(&mut self, val: Implication<L>) {
        let key = val.name();
        self.0.insert(key.into(), val);
    }

    pub fn add_all(&mut self, vals: ImplicationSet<L>) {
        for val in vals.0.into_values() {
            self.add(val);
        }
    }

    pub fn remove(&mut self, val: Implication<L>) -> Option<Implication<L>> {
        let key = val.name();
        self.0.remove(&Arc::<str>::from(key))
    }

    pub fn remove_all(&mut self, vals: ImplicationSet<L>) {
        for v in vals.0.into_values() {
            self.remove(v);
        }
    }

    /// Returns a set of candidate implications by analyzing predicate cvecs
    /// within the given e-graph, and a set of potential equalities.
    ///
    /// Equalities are found using cvec matching.
    ///
    /// Each implication is formed between two predicates `p1` and `p2` with
    /// corresponding cvecs `c1` and `c2`. A candidate implication `p1 => p2`
    /// is generated if:
    ///
    /// forall i . c1\[i\] -> c2\[i\]
    ///
    /// That is, whenever `p1` is true in a cvec (`p1 == 1`), `p2` must
    /// also be true. This forms the basis of implication via pointwise matching
    /// over cvecs (a.k.a. pvec matching).
    ///
    /// We apply aggressive pruning to avoid generating trivial or unhelpful
    /// implications. In particular:
    /// - If `c1` is always false, the implication is likely vacuously true (`LhsFalse`)
    /// - If `c2` is always true, the implication adds no new information (`RhsTrue`)
    ///
    /// See [`ImplicationValidationResult::LhsFalse`] and
    /// [`ImplicationValidationResult::RhsTrue`] for more.
    ///
    /// Returns a new `ImplicationSet` and the corresponding synthesized rules.
    // Dev Note: It's really important that the set that's returned from this consists of
    // **generalized rules**.
    pub fn pvec_match(&self, egraph: &mut EGraph<L, SynthAnalysis>) -> (Self, Ruleset<L>) {
        todo!()
    }

    /// Pops up to `step_size` best implications from the set.
    /// The selection is based on implication scores: see [`Implication::score`].
    pub fn select(&mut self, step_size: usize, invalid: &mut ImplicationSet<L>) -> Self {
        let mut chosen: Self = Default::default();
        self.0.sort_by(|_, imp1, _, imp2| {
            imp2.score()
                .partial_cmp(&imp1.score())
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // insert `step_size` best implications into the chosen set.
        while chosen.len() < step_size {
            let popped = self.0.pop();
            if let Some((_, imp)) = popped {
                if imp.is_valid() {
                    // We assume that the rule is generalized at this point.
                    chosen.add(imp.clone());
                } else {
                    invalid.add(imp.clone())
                }
            } else {
                break;
            }
        }

        assert!(chosen.len() <= step_size);
        chosen
    }

    /// Uses the prior implications and equalities to minimize the set of implications.
    /// Returns a tuple of:
    /// - The new implications that were added to the set.
    /// - The implications that were invalidated during the minimization process.
    pub fn minimize(&mut self, prior: ImplicationSet<L>, equalities: Ruleset<L>) -> (Self, Self) {
        let mut invalid = ImplicationSet::new();
        let mut chosen = prior.clone();
        let mut manager: EGraphManager<L> = EGraphManager::new();
        let step_size = 10;

        // 0. As a prior step, add the equalities and prior implications to the egraph.

        manager.add_rewrites(&equalities.clone()).unwrap();
        manager.add_implications(&prior.clone()).unwrap();

        // 1. Add the lhs, rhs of all candidates to the e-graph.
        for (_, candidate) in &self.0 {
            // this assumes that the lhs, rhs are concrete.
            manager.add_assumption(candidate.lhs().clone()).unwrap();
            manager.add_assumption(candidate.rhs().clone()).unwrap();
        }

        while !self.is_empty() {
            // 2. Run the implications and rewrites.
            manager.run_rewrite_rules();
            manager.run_implication_rules();
            let selected = self.select(step_size, &mut invalid);
            chosen.add_all(selected);

            // 3. See what merged!
            self.shrink(&mut EgglogEGraph::default());
        }

        // Return only the new implications.
        chosen.remove_all(self.clone());
        (chosen, invalid)
    }

    /// Removes implications from the set that are subsumed by any of the rules present in the e-graph.
    /// It's really important that before calling `shrink`, you run some chosen implications
    /// and equalities: otherwise this is a really expensive no-op!
    fn shrink(&mut self, egraph: &mut EgglogEGraph) {
        //    For each candidate: if there is a path from lhs --> rhs
        //    (i.e., the assumption does not contribute to the proving power of this implication set),
        //    remove it.
        for (_, imp) in &self.clone().0 {
            let lhs = imp.lhs().chop_assumption();
            let rhs = imp.rhs().chop_assumption();
            // If we can find a path from lhs to rhs, then we can remove this implication.
            match egraph.parse_and_run_program(None, &format!("(check (path {} {}))", lhs, rhs)) {
                Ok(_) => {
                    // Redundant! Get it out of here.
                    self.remove(imp.clone());
                }
                Err(e) => {
                    assert!(
                        e.to_string().contains("CheckError"),
                        "Something terrible happened while checking {}: {}",
                        imp.name(),
                        e
                    );
                }
            };
        }
    }
}

/// TESTS
#[cfg(test)]
mod select_tests {
    use crate::{conditions::assumption::Assumption, halide::Pred};

    use super::*;

    #[test]
    fn test_select() {
        let mut imp_set: ImplicationSet<Pred> = ImplicationSet::new();

        let simple_imp = Implication::new(
            "imp1".into(),
            Assumption::<Pred>::new("(< ?x 5)".to_string()).unwrap(),
            Assumption::<Pred>::new("(< ?x 10)".to_string()).unwrap(),
        ).unwrap();

        let verbose_imp = Implication::new(
            "imp2".into(),
            Assumption::<Pred>::new("(< ?x (+ 4 1))".to_string()).unwrap(),
            Assumption::<Pred>::new("(< ?x 10)".to_string()).unwrap(),
        ).unwrap();

        imp_set.add(simple_imp.clone());
        imp_set.add(verbose_imp);

        let mut invalid = ImplicationSet::new();
        let selected = imp_set.select(1, &mut invalid);
        assert_eq!(selected.len(), 1);
        assert!(invalid.is_empty());
        assert_eq!(selected.0.values().next().unwrap(), &simple_imp);

        assert!(!imp_set.contains(&simple_imp));
    }

    #[test]
    fn test_select_filters_invalid() {
        let mut imp_set: ImplicationSet<Pred> = ImplicationSet::new();

        let invalid_imp = Implication::new(
            "imp1".into(),
            Assumption::<Pred>::new("(< ?x 10)".to_string()).unwrap(),
            Assumption::<Pred>::new("(< ?x 5)".to_string()).unwrap(),
        ).unwrap();

        let valid_imp = Implication::new(
            "imp2".into(),
            Assumption::<Pred>::new("(< ?x (+ 4 1))".to_string()).unwrap(),
            Assumption::<Pred>::new("(< ?x 10)".to_string()).unwrap(),
        ).unwrap();

        imp_set.add(invalid_imp.clone());
        imp_set.add(valid_imp.clone());

        let mut invalid = ImplicationSet::new();
        let selected = imp_set.select(1, &mut invalid);
        assert_eq!(selected.len(), 1);
        assert_eq!(invalid.len(), 1);
        assert_eq!(selected.0.values().next().unwrap(), &valid_imp);
        assert_eq!(invalid.0.values().next().unwrap(), &invalid_imp);

        // it should have chosen the invalid imp, filtered it, and then
        // selected the valid one (thus removing both from the original set).
        assert!(imp_set.is_empty());
    }
}

#[cfg(test)]
mod shrink_tests {
    use super::*;
    use crate::{conditions::assumption::Assumption, halide::Pred};

    #[test]
    fn shrink_filters_identical_impl() {
        let imp = Implication::<Pred>::new(
            "imp1".into(),
            Assumption::<Pred>::new("(< ?x 0)".to_string()).unwrap(),
            Assumption::<Pred>::new("(!= ?x 0)".to_string()).unwrap(),
        ).unwrap();


        let mut imp_set: ImplicationSet<Pred> = ImplicationSet::new();
        // (x < 0) -> (x != 0)
        imp_set.add(imp.clone());

        let mut egraph = EgglogEGraph::default();
    }

    #[test]
    fn shrink_filters_redundant_impl() {
        // given (p -> q), (q -> r), we should be able to remove (p -> r)
        todo!()
    }

    #[test]
    fn shrink_keeps_useful_impl() {
        // given (p -> q), (q -> r), we should keep (p -> s)
        todo!()
    }

}