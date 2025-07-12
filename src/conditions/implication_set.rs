use std::sync::Arc;

use egg::{AstSize, EGraph, ENodeOrVar, Extractor, Id, RecExpr, Rewrite};

use egglog::EGraph as EgglogEGraph;

#[allow(unused_imports)]
use crate::{
    conditions::implication::{Implication, ImplicationValidationResult},
    enumo::Ruleset,
    IndexMap, SynthAnalysis, SynthLanguage,
};
use crate::{
    conditions::{assumption::Assumption, manager::EGraphManager},
    enumo::{Filter, Metric, Scheduler, Workload},
    CVec, Limits,
};

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
    pub fn pvec_match(egraph: &EGraph<L, SynthAnalysis>, prior: &Self) -> (Self, Ruleset<L>) {
        let mut manager: EGraphManager<L> = EGraphManager::new();
        manager.add_implications(prior).unwrap();

        // Returns true iff cvec1 --> cvec2, i.e., forall i, !cvec[i] or cvec2[i].
        let compare = |cvec1: &CVec<L>, cvec2: &CVec<L>| -> bool {
            for tup in cvec1.iter().zip(cvec2) {
                match tup {
                    (Some(a), Some(b)) => match (L::to_bool(a.clone()), L::to_bool(b.clone())) {
                        (Some(true), Some(false)) => {
                            return false;
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
            true
        };

        // we need to do pairwise comparisons of e-classes, because for each pair of eclasses
        // (i, j), we need to check both i --> j and j --> i.
        let mut by_cvec: IndexMap<&CVec<L>, Vec<Id>> = IndexMap::default();
        for class in egraph.classes() {
            if class.data.is_defined() {
                by_cvec.entry(&class.data.cvec).or_default().push(class.id);
            }
        }

        let mut imp_candidates = ImplicationSet::new();
        let mut eq_candidates: Ruleset<L> = Ruleset::default();

        let extract = Extractor::new(egraph, AstSize);

        // 1. Attempt to find equalities.
        for ids in by_cvec.values() {
            let exprs: Vec<_> = ids.iter().map(|&id| extract.find_best(id).1).collect();

            for (idx, e1) in exprs.iter().enumerate() {
                for e2 in exprs[(idx + 1)..].iter() {
                    eq_candidates.add_from_recexprs(e1, e2);
                }
            }
        }

        // 2. Attempt to find implications.
        for pvec1 in by_cvec.keys() {
            for pvec2 in by_cvec.keys() {
                if compare(pvec1, pvec2) {
                    let first_exprs: Vec<_> = by_cvec[pvec1]
                        .iter()
                        .map(|&id| extract.find_best(id).1)
                        .collect();
                    let second_exprs: Vec<_> = by_cvec[pvec2]
                        .iter()
                        .map(|&id| extract.find_best(id).1)
                        .collect();
                    for e1 in &first_exprs {
                        for e2 in &second_exprs {
                            if e1 == e2 {
                                // skip self-implications.
                                continue;
                            }
                            let name = format!("{} --> {}", e1, e2);
                            // attempt to make an implication, and if it doesn't work, skip it.

                            match (
                                Assumption::new(e1.to_string()),
                                Assumption::new(e2.to_string()),
                            ) {
                                (Ok(lhs), Ok(rhs)) => {
                                    let imp = Implication::new(name.into(), lhs, rhs);
                                    match imp {
                                        Ok(imp) => {
                                            // Include the implication as a rule, only
                                            // if it is not already subsumed by the prior implications.
                                            manager.add_assumption(imp.lhs().clone()).unwrap();
                                            manager.add_assumption(imp.rhs().clone()).unwrap();
                                            manager.run_implication_rules();
                                            if !manager.check_path(&imp.lhs(), &imp.rhs()).unwrap()
                                            {
                                                imp_candidates.add(imp);
                                            }
                                        }
                                        Err(_) => {
                                            // skip it.
                                        }
                                    }
                                }
                                // if building the implication failed, it better be because the exprs are
                                // not predicates, and not for some other terrible reason.
                                (a, b) => {
                                    if a.is_err() {
                                        assert!(a
                                            .err()
                                            .unwrap()
                                            .to_string()
                                            .contains("not a valid predicate"))
                                    }
                                    if b.is_err() {
                                        assert!(b
                                            .err()
                                            .unwrap()
                                            .to_string()
                                            .contains("not a valid predicate"))
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        (imp_candidates, eq_candidates)
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
        let step_size = 1;

        // 0. As a prior step, add the equalities and prior implications to the egraph.

        manager.add_rewrites(&equalities.clone()).unwrap();
        manager.add_implications(&prior.clone()).unwrap();

        // 1. Add the lhs, rhs of all candidates to the e-graph.
        for (_, candidate) in &self.0 {
            // this assumes that the lhs, rhs are concrete.
            manager.add_assumption(candidate.lhs().clone()).unwrap();
            manager.add_assumption(candidate.rhs().clone()).unwrap();
        }

        // We shrink here just in case the best candidate is subsumed by the prior implications.
        self.shrink(&mut manager);

        println!("prior:");
        for imp in prior.iter() {
            println!("  {}", imp.name());
        }
        while !self.is_empty() {
            // 2. Pick some candidates to include.
            let selected = self.select(step_size, &mut invalid);

            let mut actual_selected = ImplicationSet::new();
            // there's this stupid step in the middle where we have to generalize the rules.
            for imp in selected.iter() {
                let mut cache = Default::default();
                let lhs = L::generalize(&L::instantiate(&imp.lhs().chop_assumption()), &mut cache);
                let rhs = L::generalize(&L::instantiate(&imp.rhs().chop_assumption()), &mut cache);
                let lhs_assumption = Assumption::new(lhs.to_string()).unwrap();
                let rhs_assumption = Assumption::new(rhs.to_string()).unwrap();
                let generalized_imp = Implication::new(
                    format!("{} -> {}", lhs, rhs).into(),
                    lhs_assumption,
                    rhs_assumption,
                )
                .unwrap();
                actual_selected.add(generalized_imp);
            }

            // 3. Add the implications to the manager.
            manager.add_implications(&actual_selected).unwrap();
            chosen.add_all(actual_selected);

            // 4. See what merged!
            self.shrink(&mut manager);
        }

        // Return only the new implications.
        chosen.remove_all(prior.clone());
        (chosen, invalid)
    }

    /// Converts the implications in this set to a vector of Egg rewrite rules.
    pub fn to_egg_rewrites(&self) -> Vec<Rewrite<L, SynthAnalysis>> {
        self.iter().map(|imp| imp.rewrite()).collect()
    }

    /// Removes implications from the set that are subsumed by any of the rules present in the e-graph.
    /// It's really important that before calling `shrink`, you run some chosen implications
    /// and equalities: otherwise this is a really expensive no-op!
    fn shrink(&mut self, manager: &mut EGraphManager<L>) {
        manager.run_rewrite_rules();
        manager.run_implication_rules();
        //    For each candidate: if there is a path from lhs --> rhs
        //    (i.e., the assumption does not contribute to the proving power of this implication set),
        //    remove it.
        for (_, imp) in &self.clone().0 {
            if manager.check_path(&imp.lhs(), &imp.rhs()).unwrap() {
                // Redundant! Get it out of here.
                self.remove(imp.clone());
                continue;
            }
        }
    }
}

/// A useful utility function to construct a minimal set of implication rules
/// from the given workload, up to a maximum size of 7.
/// Assumes that the workload's variables are atoms.
pub fn run_implication_workload<L: SynthLanguage>(
    wkld: &Workload,
    prior: &ImplicationSet<L>,
    rules: &Ruleset<L>,
) -> ImplicationSet<L> {
    let max_size = 7;
    let mut chosen: ImplicationSet<L> = ImplicationSet::new();
    chosen.add_all(prior.clone());

    // 1. Initialize the e-graph with the variables present in the workload.
    let mut egraph: EGraph<L, SynthAnalysis> = Default::default();

    let atom_wkld = wkld.clone().filter(Filter::MetricEq(Metric::Atoms, 1));
    let mut vars: Vec<String> = vec![];

    for t in atom_wkld.force() {
        let expr: RecExpr<L> = t.to_string().parse().unwrap();
        for node in expr.as_ref() {
            if let ENodeOrVar::Var(v) = node.clone().to_enode_or_var() {
                let mut v = v.to_string();
                v.remove(0);
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
    }

    L::initialize_vars(&mut egraph, &vars);

    for size in 1..=max_size {
        let curr_workload = wkld.clone().filter(Filter::MetricEq(Metric::Atoms, size));
        for t in curr_workload.force() {
            egraph.add_expr(&t.to_string().parse::<RecExpr<L>>().unwrap());
        }
        egraph = Scheduler::Compress(Limits::minimize()).run(&egraph, rules);
        let (mut impl_candidates, _) = ImplicationSet::pvec_match(&egraph, &chosen);
        let (new_candidates, _) = impl_candidates.minimize(chosen.clone(), Ruleset::default());
        chosen.add_all(new_candidates);
    }
    chosen
}

/// TESTS
#[cfg(test)]
mod run_implication_workload_tests {
    use super::*;

    use crate::{
        enumo::{Ruleset, Workload},
        halide::Pred,
        recipe_utils::run_workload,
        Limits,
    };

    // This test checks that the implication workload runner can
    // find implications in a simple workload.
    #[test]
    fn run_implication_workload_ok() {
        let the_bools = Workload::new(&["(OP2 V V)", "V"])
            .plug("OP2", &Workload::new(&["<", "!="]))
            .plug("V", &Workload::new(&["a", "b", "c", "0"]));

        let and_wkld = Workload::new(&["(&& V V)"])
            .plug("V", &the_bools.clone())
            .append(the_bools.clone());

        let mut all_rules: Ruleset<Pred> = Ruleset::default();

        let bool_rules: Ruleset<Pred> = run_workload(
            the_bools.clone(),
            None,
            Ruleset::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
        );

        all_rules.extend(bool_rules.clone());

        let and_rules: Ruleset<Pred> = run_workload(
            Workload::new(&["(&& V V)"]).plug("V", &Workload::new(&["a", "b", "0", "1"])),
            None,
            Ruleset::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
        );

        all_rules.extend(and_rules.clone());

        let rules = run_implication_workload::<Pred>(&and_wkld, &ImplicationSet::new(), &all_rules);
    }
}

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
        )
        .unwrap();

        let verbose_imp = Implication::new(
            "imp2".into(),
            Assumption::<Pred>::new("(< ?x (+ 4 1))".to_string()).unwrap(),
            Assumption::<Pred>::new("(< ?x 10)".to_string()).unwrap(),
        )
        .unwrap();

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
        )
        .unwrap();

        let valid_imp = Implication::new(
            "imp2".into(),
            Assumption::<Pred>::new("(< ?x (+ 4 1))".to_string()).unwrap(),
            Assumption::<Pred>::new("(< ?x 10)".to_string()).unwrap(),
        )
        .unwrap();

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
mod minimize_tests {
    use super::*;
    use crate::{conditions::assumption::Assumption, halide::Pred};

    #[test]
    fn minimize_filters_identical_impl() {
        let mut candidate_set: ImplicationSet<Pred> = ImplicationSet::new();
        candidate_set.add(
            Implication::<Pred>::new(
                "imp1".into(),
                Assumption::<Pred>::new("(< x 0)".to_string()).unwrap(),
                Assumption::<Pred>::new("(!= x 0)".to_string()).unwrap(),
            )
            .unwrap(),
        );
        candidate_set.add(
            Implication::<Pred>::new(
                "imp2".into(),
                Assumption::<Pred>::new("(< x 0)".to_string()).unwrap(),
                Assumption::<Pred>::new("(!= x 0)".to_string()).unwrap(),
            )
            .unwrap(),
        );

        let existing_set = ImplicationSet::new();

        let mut manager: EGraphManager<Pred> = EGraphManager::new();
        manager.add_implications(&existing_set).unwrap();
        let (remaining, invalid) = candidate_set.minimize(existing_set, Ruleset::default());
        assert!(invalid.is_empty());
        // there should be one implication that is new.
        assert_eq!(remaining.len(), 1);
    }

    #[test]
    fn minimize_filters_redundant_impl() {
        let mut candidate_set: ImplicationSet<Pred> = ImplicationSet::new();
        // Rules look weird af because I want to make sure that it picks `imp1` and `imp2` before `imp3`.
        // Byeah.
        candidate_set.add(
            Implication::<Pred>::new(
                "imp1".into(),
                Assumption::<Pred>::new("(< x (+ 0 0))".to_string()).unwrap(),
                Assumption::<Pred>::new("(!= x 0)".to_string()).unwrap(),
            )
            .unwrap(),
        );
        candidate_set.add(
            Implication::<Pred>::new(
                "imp2".into(),
                Assumption::<Pred>::new("(!= x 0)".to_string()).unwrap(),
                Assumption::<Pred>::new("(!= x (+ 0 (+ 0 0)))".to_string()).unwrap(),
            )
            .unwrap(),
        );
        candidate_set.add(
            Implication::<Pred>::new(
                "imp3".into(),
                Assumption::<Pred>::new("(< x (+ 0 0))".to_string()).unwrap(),
                Assumption::<Pred>::new("(!= x (+ 0 (+ 0 0)))".to_string()).unwrap(),
            )
            .unwrap(),
        );

        let existing_set = ImplicationSet::new();

        let mut manager: EGraphManager<Pred> = EGraphManager::new();
        manager.add_implications(&existing_set).unwrap();
        let (remaining, invalid) = candidate_set.minimize(existing_set, Ruleset::default());
        assert!(invalid.is_empty());
        // there should be one implication that is new.
        assert_eq!(remaining.len(), 2);
        assert!(remaining.iter().all(|imp| imp.name() != "imp3"));
    }

    #[test]
    fn minimize_keeps_useful_impl() {
        // given (p -> q), (q -> r), we should keep (p -> s)
        let mut candidate_set: ImplicationSet<Pred> = ImplicationSet::new();
        // Rules look weird af because I want to make sure that it picks `imp1` and `imp2` before `imp3`.
        // Byeah.
        candidate_set.add(
            Implication::<Pred>::new(
                "imp1".into(),
                Assumption::<Pred>::new("(< x (+ 0 0))".to_string()).unwrap(),
                Assumption::<Pred>::new("(!= x 0)".to_string()).unwrap(),
            )
            .unwrap(),
        );
        candidate_set.add(
            Implication::<Pred>::new(
                "imp2".into(),
                Assumption::<Pred>::new("(!= x 0)".to_string()).unwrap(),
                Assumption::<Pred>::new("(!= x (+ 0 (+ 0 0)))".to_string()).unwrap(),
            )
            .unwrap(),
        );
        candidate_set.add(
            Implication::<Pred>::new(
                "imp3".into(),
                Assumption::<Pred>::new("(< x (+ 0 0))".to_string()).unwrap(),
                Assumption::<Pred>::new("(< x 1)".to_string()).unwrap(),
            )
            .unwrap(),
        );

        let existing_set = ImplicationSet::new();

        let mut manager: EGraphManager<Pred> = EGraphManager::new();
        manager.add_implications(&existing_set).unwrap();
        let (remaining, invalid) = candidate_set.minimize(existing_set, Ruleset::default());
        assert!(invalid.is_empty());
        // there should be one implication that is new.
        assert_eq!(remaining.len(), 3);
    }
}

#[cfg(test)]
mod pvec_match_tests {
    use egg::EGraph;

    use crate::{
        conditions::implication_set::ImplicationSet,
        enumo::{Ruleset, Scheduler, Workload},
        halide::Pred,
        recipe_utils::run_workload,
        Limits, SynthAnalysis,
    };

    // A big ass integration test that puts it all together and sees if given a moderate
    // workload, it can synthesize implications and equalities AND minimize them.
    #[test]
    fn pvec_match_ok() {
        // Define a workload of predicates.
        let the_ints = Workload::new(&["V", "(OP2 V V)"])
            .plug("V", &Workload::new(&["a", "b", "0"]))
            .plug("OP2", &Workload::new(&["min", "max", "+"]));

        let the_bools = Workload::new(&["(OP2 V V)"])
            .plug("V", &the_ints)
            .plug("OP2", &Workload::new(&["<=", "<"]))
            .append(
                Workload::new(&["(&& (OP2 a 0) (OP2 b 0))"])
                    .plug("OP2", &Workload::new(&["<", "<=", ">", ">="])),
            );

        println!("wkld length: {}", the_bools.force().len());

        let mut all_rules: Ruleset<Pred> = Ruleset::default();

        let bool_rules: Ruleset<Pred> = run_workload(
            the_bools.clone(),
            None,
            Ruleset::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
        );

        all_rules.extend(bool_rules.clone());

        let and_rules: Ruleset<Pred> = run_workload(
            Workload::new(&["(&& V V)"]).plug("V", &Workload::new(&["a", "b", "0", "1"])),
            None,
            Ruleset::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
        );

        all_rules.extend(and_rules.clone());

        let egraph: EGraph<Pred, SynthAnalysis> = the_bools.to_egraph();
        println!("egraph size: {}", egraph.number_of_classes());
        let egraph = Scheduler::Compress(Limits::minimize()).run(&egraph, &all_rules);
        println!(
            "egraph size after compression: {}",
            egraph.number_of_classes()
        );
        // let (mut imps, rules) = ImplicationSet::pvec_match(&egraph);

        // let (imps, _invalid) = imps.minimize(ImplicationSet::new(), rules.clone());

        // println!("imps:");
        // for imp in imps.iter() {
        //     println!("{}", imp.name());
        // }
    }
}
