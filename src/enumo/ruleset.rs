use egg::{Analysis, AstSize, EClass, Extractor, Language, RecExpr, Rewrite, Runner, Searcher};
use indexmap::map::{IntoIter, Iter, IterMut, Values, ValuesMut};
use rayon::iter::IntoParallelIterator;
use rayon::prelude::ParallelIterator;
use std::{fmt::Display, io::Write, sync::Arc};

use crate::{
    conditions::{assumption::Assumption, implication_set::ImplicationSet},
    CVec, DeriveType, EGraph, ExtractableAstSize, HashMap, Id, IndexMap, Limits, PVec, Signature,
    SynthAnalysis, SynthLanguage,
};

use super::{Rule, Scheduler};

/// A mapping from pvecs to their corresponding predicates.
pub type PredicateMap<L> = IndexMap<PVec, Vec<Assumption<L>>>;

/// A set of rewrite rules
#[derive(Clone, Debug)]
pub struct Ruleset<L: SynthLanguage>(pub IndexMap<Arc<str>, Rule<L>>);

impl<L: SynthLanguage> PartialEq for Ruleset<L> {
    fn eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        for ((name1, _), (name2, _)) in self.0.iter().zip(other.0.iter()) {
            if name1 != name2 {
                return false;
            }
        }
        true
    }
}

impl<L: SynthLanguage> Default for Ruleset<L> {
    fn default() -> Self {
        Self(IndexMap::default())
    }
}

impl<L: SynthLanguage> IntoIterator for Ruleset<L> {
    type Item = (Arc<str>, Rule<L>);
    type IntoIter = IntoIter<Arc<str>, Rule<L>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, L: SynthLanguage> IntoIterator for &'a Ruleset<L> {
    type Item = (&'a Arc<str>, &'a Rule<L>);
    type IntoIter = Iter<'a, Arc<str>, Rule<L>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, L: SynthLanguage> IntoIterator for &'a mut Ruleset<L> {
    type Item = (&'a Arc<str>, &'a mut Rule<L>);
    type IntoIter = IterMut<'a, Arc<str>, Rule<L>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<L: SynthLanguage> Ruleset<L> {
    pub fn new<I>(vals: I) -> Self
    where
        I: IntoIterator,
        I::Item: AsRef<str>,
    {
        let mut map = IndexMap::default();
        for v in vals {
            if let Ok((forwards, backwards)) = Rule::from_string(v.as_ref()) {
                map.insert(forwards.name.clone(), forwards);
                if let Some(backwards) = backwards {
                    map.insert(backwards.name.clone(), backwards);
                }
            }
        }
        Ruleset(map)
    }

    pub fn union(&self, other: &Self) -> Self {
        let mut map = self.0.clone();
        map.extend(other.0.clone());
        Ruleset(map)
    }

    pub fn iter(&self) -> Values<'_, Arc<str>, Rule<L>> {
        self.0.values()
    }

    pub fn iter_mut(&mut self) -> ValuesMut<'_, Arc<str>, Rule<L>> {
        self.0.values_mut()
    }

    pub fn to_str_vec(&self) -> Vec<String> {
        match self {
            Ruleset(m) => m.iter().map(|(name, _val)| name.to_string()).collect(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn condition_len(&self) -> usize {
        let mut size = 0;
        for (_, rule) in &self.0 {
            if rule.cond.is_some() {
                size += 1;
            }
        }
        size
    }

    pub fn bidir_len(&self) -> usize {
        let mut bidir = 0;
        let mut unidir = 0;
        for (_, rule) in &self.0 {
            if rule.cond.is_some() {
                continue;
            }
            let reverse = if let Some(c) = &rule.cond {
                Rule::new_cond(&rule.rhs, &rule.lhs, c, rule.true_count)
            } else {
                Rule::new(&rule.rhs, &rule.lhs)
            };
            if reverse.is_some() && self.contains(&reverse.unwrap()) {
                bidir += 1;
            } else {
                unidir += 1;
            }
        }
        unidir + (bidir / 2)
    }

    pub fn contains(&self, rule: &Rule<L>) -> bool {
        self.0.contains_key(&rule.name)
    }

    pub fn add(&mut self, rule: Rule<L>) {
        self.0.insert(rule.name.clone(), rule);
    }

    pub fn add_cond_from_recexprs(
        &mut self,
        e1: &RecExpr<L>,
        e2: &RecExpr<L>,
        cond: &RecExpr<L>,
        true_count: usize,
    ) {
        let map = &mut HashMap::default();
        let l_pat = L::generalize(e1, map);
        let r_pat = L::generalize(e2, map);
        let cond = Assumption::new(L::generalize(cond, map).to_string()).unwrap();
        let forward = Rule::new_cond(&l_pat, &r_pat, &cond, Some(true_count));
        let backward = Rule::new_cond(&r_pat, &l_pat, &cond, Some(true_count));
        println!("[add_cond_from_recexprs] Adding rule candidate: {l_pat} ==> {r_pat} if {cond}");
        if let Some(forward) = forward {
            self.add(forward);
        }
        if let Some(backward) = backward {
            self.add(backward);
        }
    }

    /// Given a pair of recexprs, try to add rule candidates representing both
    /// directions (e1 ==> e2 and e2 ==> e1)
    /// This is actually a little bit subtle because it is important that we
    /// reuse the same generalized patterns for both directions.
    /// That is, this function *is not* equivalent to calling
    /// add(Rule::from_recexprs(e1, e2)); add(Rule::from_recexprs(e2, e1))
    pub fn add_from_recexprs(&mut self, e1: &RecExpr<L>, e2: &RecExpr<L>) {
        let map = &mut HashMap::default();
        let l_pat = L::generalize(e1, map);
        let r_pat = L::generalize(e2, map);
        let forward = Rule::new(&l_pat, &r_pat);
        let backward = Rule::new(&r_pat, &l_pat);
        if let Some(forward) = forward {
            self.add(forward);
        }
        if let Some(backward) = backward {
            self.add(backward);
        }
    }

    pub fn add_all(&mut self, rules: Vec<&Rule<L>>) {
        for rule in rules {
            self.add(rule.clone());
        }
    }

    pub fn remove_all(&mut self, other: Self) {
        for (name, _) in other.0 {
            self.0.remove(&name);
        }
    }

    pub fn extend(&mut self, other: Self) {
        self.0.extend(other.0)
    }

    /// Partition a ruleset by applying a predicate function to each rule in the ruleset
    pub fn partition<F>(&self, f: F) -> (Self, Self)
    where
        F: Fn(&Rule<L>) -> bool + std::marker::Sync,
    {
        let rules: Vec<&Rule<L>> = self.0.values().collect();
        let (yeses, nos): (Vec<_>, Vec<_>) = rules.into_par_iter().partition(|rule| f(rule));
        let mut yes = Ruleset::default();
        let mut no = Ruleset::default();
        yes.add_all(yeses);
        no.add_all(nos);
        (yes, no)
    }

    pub fn to_file(&self, filename: &str) {
        let mut file = std::fs::File::create(filename)
            .unwrap_or_else(|_| panic!("Failed to open '{}'", filename));
        for (name, _) in &self.0 {
            writeln!(file, "{name}").expect("Unable to write");
        }
    }

    pub fn from_file(filename: &str) -> Self {
        let infile = std::fs::File::open(filename).expect("can't open file");
        let reader = std::io::BufReader::new(infile);
        let mut all_rules = IndexMap::default();
        for line in std::io::BufRead::lines(reader) {
            let line = line.unwrap();
            if let Ok((forwards, backwards)) = Rule::from_string(&line) {
                all_rules.insert(forwards.name.clone(), forwards);
                if let Some(backwards) = backwards {
                    all_rules.insert(backwards.name.clone(), backwards);
                }
            }
        }
        Self(all_rules)
    }

    pub fn pretty_print(&self) {
        let mut strs = vec![];
        for (name, rule) in &self.0 {
            let reverse = if rule.cond.is_some() {
                Rule::new_cond(
                    &rule.rhs,
                    &rule.lhs,
                    &rule.cond.clone().unwrap(),
                    rule.true_count,
                )
            } else {
                Rule::new(&rule.rhs, &rule.lhs)
            };
            if reverse.is_some() && self.contains(&reverse.unwrap()) {
                let cond_display = if rule.cond.is_some() {
                    let cond_display = rule.cond.clone().unwrap().to_string();
                    assert!(
                        cond_display.starts_with(format!("({}", L::assumption_label()).as_str())
                    );
                    // remove the starting prefix and the last )
                    format!(
                        " if {}",
                        &cond_display
                            [format!("({}", L::assumption_label()).len()..cond_display.len() - 1]
                    )
                } else {
                    "".to_string()
                };
                let reverse_name = format!("{} <=> {}{}", rule.rhs, rule.lhs, cond_display);
                if !strs.contains(&reverse_name) {
                    strs.push(format!("{} <=> {}{}", rule.lhs, rule.rhs, cond_display));
                }
            } else {
                strs.push(name.to_string());
            }
        }

        for s in strs {
            println!("{s}");
        }
    }

    /// Find candidates from two e-graphs
    ///
    /// If extracted terms l and r are in the same e-class in eg2,
    /// but in different e-classes in eg1,
    /// l=>r will be extracted as a rule candidate.
    ///
    /// This function should only be called on a pair of e-graphs such that
    /// eg2 is the result of applying a ruleset to eg1.
    pub fn extract_candidates(
        eg1: &EGraph<L, SynthAnalysis>,
        eg2: &EGraph<L, SynthAnalysis>,
    ) -> Self {
        let mut candidates = Ruleset::default();
        let ids: Vec<Id> = eg1.classes().map(|c| c.id).collect();
        let mut unions = HashMap::default();
        for id in ids {
            let new_id = eg2.find(id);
            unions.entry(new_id).or_insert_with(Vec::new).push(id);
        }

        let clone = eg1.clone();
        let extract = Extractor::new(&clone, ExtractableAstSize);

        for ids in unions.values() {
            for id1 in ids.clone() {
                for id2 in ids.clone() {
                    let (c1, e1) = extract.find_best(id1);
                    let (c2, e2) = extract.find_best(id2);
                    if c1 == usize::MAX || c2 == usize::MAX {
                        continue;
                    }
                    if e1 != e2 {
                        candidates.add_from_recexprs(&e1, &e2);
                    }
                }
            }
        }
        candidates
    }

    /// Returns a ruleset of *conditional* rewrite candidates.
    ///
    /// Most users will want to use `run_workload` or `recursive_rules`
    /// instead of calling this.
    ///
    /// This is an extension of `cvec_match` that uses *predicate vectors* ("pvecs")
    /// to define conditional equivalence between cvecs. A predicate vector is a
    /// boolean mask indicating under which observations (positions) two cvecs should agree.
    ///
    /// Two cvecs, `cvec1` and `cvec2`, are considered conditionally equivalent under a
    /// predicate vector `pvec` if: pvec[i] --> (cvec1[i] == cvec2[i])
    ///
    /// That is, for every index `i` where `pvec[i]` is true, the corresponding values
    /// in `cvec1` and `cvec2` must be equal.
    ///
    /// ⚠️ Note: This implication is **not symmetric** — we only require that the condition
    /// is **sufficient** to guarantee equivalence, not necessary. As a result, this
    /// generates *conditional rewrite candidates* where the condition enables the rule,
    /// but doesn't exhaustively characterize it.
    pub fn conditional_cvec_match(
        egraph: &EGraph<L, SynthAnalysis>,
        prior: &Self,
        conditions: &PredicateMap<L>,
        implications: &ImplicationSet<L>,
    ) -> Self {
        let start_time = std::time::Instant::now();

        let by_cvec = Self::group_classes_by_cvec(egraph);
        let mut candidates = Ruleset::default();
        let extract = Extractor::new(egraph, AstSize);

        println!(
            "[conditional_cvec_match] Starting conditional cvec match with {} unique cvecs and {} pvecs.",
            by_cvec.len(),
            conditions.len()
        );
        let mut skipped_rules = 0;

        let mut predicate_to_egraph: IndexMap<String, EGraph<L, SynthAnalysis>> =
            IndexMap::default();

        let mut i = 0;
        for cvec1 in by_cvec.keys() {
            assert_eq!(cvec1.len(), conditions.keys().next().unwrap().len());
            i += 1;
            for cvec2 in by_cvec.keys().skip(i) {
                // 1. For each pair of unequal cvecs, find the conditions that imply their equality.
                let predicates =
                    Self::find_matching_conditions(cvec1.clone(), cvec2.clone(), conditions);

                for id1 in by_cvec[cvec1].clone() {
                    for id2 in by_cvec[cvec2].clone() {
                        // 2. Go through each pair of terms with the corresponding cvecs.
                        let (c1, e1) = extract.find_best(id1);
                        let (c2, e2) = extract.find_best(id2);

                        if c1 == usize::MAX || c2 == usize::MAX {
                            continue;
                        }

                        // These aren't actually the rules. They're the RecExprs that the rules
                        // are built from. You'll see.
                        let mut conditional_candidates: Vec<(
                            RecExpr<L>,
                            RecExpr<L>,
                            RecExpr<L>,
                            usize,
                        )> = vec![];

                        for predicate in &predicates {
                            let true_count = conditions
                                .iter()
                                .find(|(_, patterns)| patterns.contains(predicate))
                                .unwrap()
                                .0
                                .iter()
                                .filter(|&&x| x)
                                .count();

                            let pred_string = predicate.to_string();
                            let mini_egraph = predicate_to_egraph
                                .entry(pred_string.clone())
                                .or_insert_with(|| {
                                    Self::construct_conditional_egraph(
                                        egraph,
                                        prior,
                                        &predicate.clone(),
                                        implications,
                                    )
                                })
                                .clone();

                            // 3. If the terms are equivalent under that condition with respect
                            //    to the prior rules, discard it.
                            let result = Self::get_canonical_conditional_rule(
                                &e1,
                                &e2,
                                &predicate.clone(),
                                &mini_egraph.clone(),
                            );

                            if result.is_none() {
                                skipped_rules += 1;
                                continue;
                            }

                            // 4. Validate the rule. If it's invalid, chuck it.
                            let mut dummy: Ruleset<L> = Default::default();
                            dummy.add_cond_from_recexprs(
                                &e1,
                                &e2,
                                &predicate.chop_assumption().to_string().parse().unwrap(),
                                true_count,
                            );

                            if dummy.is_empty() {
                                continue;
                            }

                            let candidate = dummy.iter().next().unwrap();
                            if !candidate.is_valid() {
                                continue;
                            }

                            // 5. See if there exists a valid rule in `conditional_candidates`
                            // that subsumes this one, or if our rule subsumes any of theirs.
                            let mut should_add = true;
                            let mut should_remove: Vec<(
                                RecExpr<L>,
                                RecExpr<L>,
                                RecExpr<L>,
                                usize,
                            )> = vec![];
                            for (l, r, c, tc) in conditional_candidates.iter() {
                                if l == &e1 && r == &e2 {
                                    // 5a:
                                    // If the condition is an assumption in our egraph, then
                                    // our condition implies theirs (our condition is stronger),
                                    // so we should remove ours and keep theirs.
                                    if mini_egraph
                                        .lookup_expr(
                                            &format!(
                                                "({} {})",
                                                L::assumption_label(),
                                                c.to_string()
                                            )
                                            .parse()
                                            .unwrap(),
                                        )
                                        .is_some()
                                    {
                                        skipped_rules += 1;
                                        should_add = false;
                                        break;
                                    }

                                    // If their condition is an assumption in our egraph, then
                                    // their condition implies ours (our condition is weaker),
                                    // so we should remove theirs and keep ours.
                                    if mini_egraph.lookup_expr(&predicate.clone().into()).is_some()
                                    {
                                        should_remove.push((l.clone(), r.clone(), c.clone(), *tc));
                                    }
                                }
                            }

                            if !should_remove.is_empty() && !should_add {
                                // an invariant is violated. i don't know what that invariant is yet.
                                panic!("this should never happen");
                            }

                            for grouping in should_remove.iter() {
                                let idx = conditional_candidates
                                    .iter()
                                    .position(|x| {
                                        x.0 == grouping.0
                                            && x.1 == grouping.1
                                            && x.2 == grouping.2
                                            && x.3 == grouping.3
                                    })
                                    .unwrap();
                                conditional_candidates.swap_remove(idx);
                            }
                            if should_add {
                                // 6. If the current candidates do not already imply
                                //    this candidate, add it to the set of conditional candidates.
                                conditional_candidates.push((
                                    e1.clone(),
                                    e2.clone(),
                                    predicate
                                        .clone()
                                        .chop_assumption()
                                        .to_string()
                                        .parse()
                                        .unwrap(),
                                    true_count,
                                ));
                            }
                        }

                        // 7. Add the conditional candidates to the candidates set.
                        for (l, r, c, tc) in conditional_candidates {
                            candidates.add_cond_from_recexprs(&l, &r, &c, tc);
                        }
                    }
                }
            }
        }

        println!(
            "[conditional_cvec_match] Found {} candidates in {} ms, skipped {} rules.",
            candidates.len(),
            start_time.elapsed().as_millis(),
            skipped_rules
        );

        candidates
    }

    // for predicate in predicates {
    //     // the true count is how many times the condition is true.
    //     let true_count = conditions
    //         .iter()
    //         .find(|(_, patterns)| patterns.contains(&predicate))
    //         .unwrap()
    //         .0
    //         .iter()
    //         .filter(|&&x| x)
    //         .count();

    //     for id1 in by_cvec[cvec1].clone() {
    //         for id2 in by_cvec[cvec2].clone() {
    //             // 3. Go through each pair of terms with the corresponding cvecs.
    //             let (c1, e1) = extract.find_best(id1);
    //             let (c2, e2) = extract.find_best(id2);

    //             if c1 == usize::MAX || c2 == usize::MAX {
    //                 continue;
    //             }

    //             // 4. If the terms are equivalent under that condition with respect
    //             //    to the prior rules, discard it.
    //             let result = Self::get_canonical_conditional_rule(
    //                 &e1,
    //                 &e2,
    //                 &predicate.clone(),
    //                 &mini_egraph.clone(),
    //             );

    //             if result.is_none() {
    //                 skipped_rules += 1;
    //                 continue;
    //             }

    //             let (e1, e2) = result.unwrap();

    //             // 5. For the candidates we've added linking `e1`, `e2`,
    //             //    check if any of the candidates imply our current candidate.
    //             let mut dummy: Ruleset<L> = Ruleset::default();
    //             let pred: RecExpr<L> =
    //                 predicate.chop_assumption().to_string().parse().unwrap();
    //             dummy.add_cond_from_recexprs(&e1, &e2, &pred, true_count);

    //             let dummy_rule = dummy.0.values().next().unwrap();
    //             if !dummy_rule.is_valid() {
    //                 // If the rule is not valid, skip it.
    //                 skipped_rules += 1;
    //                 continue;
    //             }

    //             // 4. If the current candidates do not already imply
    //             //    this candidate, add it to the set of conditional candidates.
    //             let mut should_add = true;
    //             let mut should_remove = vec![];

    //             {
    //                 for (added_lhs, added_rhs, added_cond, added_true_count) in
    //                     conditional_candidates.iter()
    //                 {
    //                     if added_lhs == &e1 && added_rhs == &e2 {
    //                         let condition_egraph = predicate_to_egraph
    //                             .get(added_cond.to_string().as_str())
    //                             .unwrap();

    //                         // If their condition is an assumption in our egraph, then
    //                         // our condition implies theirs (our condition is stronger),
    //                         // so we should remove ours and keep theirs.
    //                         if mini_egraph
    //                             .lookup_expr(
    //                                 &format!(
    //                                     "({} {added_cond})",
    //                                     L::assumption_label()
    //                                 )
    //                                 .parse()
    //                                 .unwrap(),
    //                             )
    //                             .is_some()
    //                         {
    //                             skipped_rules += 1;
    //                             should_add = false;
    //                             break;
    //                         }

    //                         // If our condition is an assumption in their egraph, then
    //                         // their condition implies ours (our condition is weaker),
    //                         // so we should remove theirs and keep ours.
    //                         if condition_egraph
    //                             .lookup_expr(&predicate.clone().into())
    //                             .is_some()
    //                         {
    //                             should_remove.push((
    //                                 added_lhs.clone(),
    //                                 added_rhs.clone(),
    //                                 added_cond.clone(),
    //                                 added_true_count,
    //                             ));
    //                         }
    //                     }
    //                 } // for loop ends here
    //             } // block ends here
    //             if !should_remove.is_empty() && !should_add {
    //                 // an invariant is violated. i don't know what that is.
    //                 panic!("this should never happen");
    //             }
    //             for grouping in should_remove.iter() {
    //                 let idx = {
    //                     conditional_candidates
    //                         .clone()
    //                         .iter()
    //                         .position(|x| {
    //                             x.0 == grouping.0
    //                                 && x.1 == grouping.1
    //                                 && x.2 == grouping.2
    //                                 && x.3 == *grouping.3
    //                         })
    //                         .unwrap()
    //                 }; // <-- Immutable borrow ends here

    //                 conditional_candidates.swap_remove(idx); // ✅ now it's safe to mutably borrow
    //             }

    //             if should_add {
    //                 candidates.add_cond_from_recexprs(&e1, &e2, &pred, true_count);
    //             }
    //         }
    //     }
    // }

    // Given a candidate conditional rule an an e-graph modeling the world under
    // the assumption of `candidate`, returns if the candidate models a new
    // conditional rule.
    //
    // If the return value is None, don't add it.
    // If the return value is (Some(lhs), Some(rhs)), then lhs/rhs
    // are the syntactically smallest representations of the e-classes
    // that the candidate's LHS/RHS map to in the egraph.
    //
    // Panics if the candidate is not a conditional rule, or if the LHS/RHS of the
    // candidate are not present in the egraph.
    fn get_canonical_conditional_rule(
        l_expr: &RecExpr<L>,
        r_expr: &RecExpr<L>,
        // TODO: let's figure out if we actually need `cond`; it seems
        // like we only pass it in for logging.
        _cond: &Assumption<L>,
        egraph: &EGraph<L, SynthAnalysis>,
    ) -> Option<(RecExpr<L>, RecExpr<L>)> {
        let l_id = egraph
            .lookup_expr(l_expr)
            .unwrap_or_else(|| panic!("Did not find {}", l_expr));

        let r_id = egraph
            .lookup_expr(r_expr)
            .unwrap_or_else(|| panic!("Did not find {}", r_expr));

        // 2. check if the lhs and rhs are equivalent in the egraph
        if l_id == r_id {
            // e1 and e2 are equivalent in the condition egraph
            // println!(
            //     "[conditional_cvec_match] Skipping {} and {} because they are equivalent in the egraph representing {}",
            //     l_expr, r_expr, cond.pat
            // );
            return None;
        }

        let extractor = Extractor::new(egraph, AstSize);
        let (_, e1) = extractor.find_best(l_id);
        let (_, e2) = extractor.find_best(r_id);

        Some((e1, e2))
    }

    // Given a "black egraph" purely modeling non-conditional equalities, a predicate, and an implication
    // set modeling conditional implications, constructs a new egraph that models the equalities
    // that hold under the given predicate.
    fn construct_conditional_egraph(
        black_egraph: &EGraph<L, SynthAnalysis>,
        prior: &Ruleset<L>,
        predicate: &Assumption<L>,
        impl_rules: &ImplicationSet<L>,
    ) -> EGraph<L, SynthAnalysis> {
        let mut colored_egraph = black_egraph.clone();

        // 1. Add the predicate to the egraph.
        predicate.insert_into_egraph(&mut colored_egraph);

        // 2. Run the implication rules on the egraph.
        let rules = impl_rules.to_egg_rewrites();

        let runner: Runner<L, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(colored_egraph.clone())
            .run(&rules)
            .with_node_limit(500);

        // 3. If we can compress the egraph further, do so.
        //    This might not be a bad place to use a `Scheduler::Saturating` instead.
        Scheduler::Compress(Limits::minimize()).run(&runner.egraph, prior)
    }

    // Given two cvecs and a mapping from pvecs to expressions, returns a list of predicates
    // which observationally imply the equality of the two cvecs.
    fn find_matching_conditions(
        cvec1: CVec<L>,
        cvec2: CVec<L>,
        pvec_to_patterns: &PredicateMap<L>,
    ) -> Vec<Assumption<L>> {
        let equal_vec: Vec<bool> = cvec1
            .iter()
            .zip(cvec2.iter())
            .map(|(a, b)| a == b)
            .collect();

        if equal_vec.iter().all(|x| *x) || equal_vec.iter().all(|x| !*x) {
            // If the condition equating the cvec is trivially true or false,
            // don't return any conditions.
            return vec![];
        }

        // find all conditions under which cvec1 == cvec2.
        let pvecs: Vec<PVec> = pvec_to_patterns
            .keys()
            .filter(|pvec| {
                pvec.iter()
                    .zip(equal_vec.iter())
                    .all(|(pvec_el, equal_el)| {
                        // if the pvec is a sufficient condition, then pvec -> equal_el.
                        // if the pvec is a necessary condition, then equal_el -> pvec (and we don't check for that).
                        !pvec_el || *equal_el
                    })
            })
            .cloned()
            .collect();

        // sort pvecs by how often they are true; vectors with more true values should come first.
        let mut pvecs: Vec<_> = pvecs
            .iter()
            .map(|pvec| (pvec, pvec.iter().filter(|&&x| x).count()))
            .collect();
        pvecs.sort_by(|(_, count1), (_, count2)| count2.cmp(count1));

        // for each pvec, find the patterns that match it
        let mut conditions: Vec<_> = vec![];
        for (pvec, _) in pvecs {
            if let Some(patterns) = pvec_to_patterns.get(pvec) {
                // for each pattern, add it to the conditions
                for pattern in patterns {
                    // we only want to add the condition if it is not already in the list
                    if !conditions.contains(pattern) {
                        conditions.push(pattern.clone());
                    }
                }
            }
        }
        conditions
    }

    // Takes the given e-graph and returns a mapping from cvecs to the e-classes with that
    // cvec.
    fn group_classes_by_cvec(egraph: &EGraph<L, SynthAnalysis>) -> IndexMap<CVec<L>, Vec<Id>> {
        let mut by_cvec: IndexMap<CVec<L>, Vec<Id>> = IndexMap::default();
        for class in egraph.classes() {
            if class.data.is_defined() {
                by_cvec
                    .entry(class.data.cvec.clone())
                    .or_default()
                    .push(class.id);
            }
        }
        by_cvec
    }

    /// Find candidates by CVec matching
    /// Pairs of e-classes with equivalent CVecs are rule candidates.
    pub fn cvec_match(egraph: &EGraph<L, SynthAnalysis>) -> Self {
        let time_start = std::time::Instant::now();
        // cvecs [𝑎1, . . . , 𝑎𝑛] and [𝑏1, . . . , 𝑏𝑛] match iff:
        // ∀𝑖. 𝑎𝑖 = 𝑏𝑖 ∨ 𝑎𝑖 = null ∨ 𝑏𝑖 = null and ∃𝑖. 𝑎𝑖 = 𝑏𝑖 ∧ 𝑎𝑖 ≠ null ∧ 𝑏𝑖 ≠ null

        println!(
            "starting cvec match with {} eclasses",
            egraph.number_of_classes()
        );

        let not_all_none: Vec<&EClass<L, Signature<L>>> = egraph
            .classes()
            .filter(|x| x.data.cvec.iter().any(|v| v.is_some()))
            .collect();

        let compare = |cvec1: &CVec<L>, cvec2: &CVec<L>| -> bool {
            for tup in cvec1.iter().zip(cvec2) {
                match tup {
                    (Some(a), Some(b)) if a != b => return false,
                    _ => (),
                }
            }
            true
        };
        let mut candidates = Ruleset::default();
        let extract = Extractor::new(egraph, AstSize);
        let mut by_first: IndexMap<Option<L::Constant>, Vec<Id>> = IndexMap::default();
        for class in &not_all_none {
            by_first
                .entry(class.data.cvec[0].clone())
                .or_insert_with(Vec::new)
                .push(class.id);
        }

        let empty = vec![];
        let first_none = by_first.get(&None).cloned().unwrap_or(empty);

        for (value, classes) in by_first {
            let mut all_classes = classes.clone();
            if value.is_some() {
                all_classes.extend(first_none.clone());
            }

            for i in 0..all_classes.len() {
                for j in i + 1..all_classes.len() {
                    let class1 = &egraph[all_classes[i]];
                    let class2 = &egraph[all_classes[j]];
                    if compare(&class1.data.cvec, &class2.data.cvec) {
                        let (_, e1) = extract.find_best(class1.id);
                        let (_, e2) = extract.find_best(class2.id);
                        candidates.add_from_recexprs(&e1, &e2);
                    }
                }
            }
        }

        println!(
            "cvec match finished in {} ms",
            time_start.elapsed().as_millis()
        );

        candidates
    }

    // TODO: Figure out what to do with this- it doesn't match the definition
    // of cvec matching from the paper, but it is faster.
    /// Faster version of CVec matching. May underestimate candidates when there are None values
    pub fn fast_cvec_match(egraph: &EGraph<L, SynthAnalysis>, prior: Ruleset<L>) -> Ruleset<L> {
        let mut by_cvec: IndexMap<&CVec<L>, Vec<Id>> = IndexMap::default();

        for class in egraph.classes() {
            if class.data.is_defined() {
                by_cvec.entry(&class.data.cvec).or_default().push(class.id);
            }
        }

        let mut candidates = Ruleset::default();
        let extract = Extractor::new(egraph, AstSize);

        for ids in by_cvec.values() {
            let exprs: Vec<_> = ids.iter().map(|&id| extract.find_best(id).1).collect();

            for (idx, e1) in exprs.iter().enumerate() {
                for e2 in exprs[(idx + 1)..].iter() {
                    // when the limits get high, we get a lot of candidates which should simplify.
                    let mut mini_egraph: EGraph<L, SynthAnalysis> = EGraph::default();
                    let l = mini_egraph.add_expr(&e1.to_string().parse().unwrap());
                    let r = mini_egraph.add_expr(&e2.to_string().parse().unwrap());
                    let runner: Runner<L, SynthAnalysis> = Runner::default()
                        .with_egraph(mini_egraph.clone())
                        .run(
                            &prior
                                .iter()
                                .map(|rule| rule.rewrite.clone())
                                .collect::<Vec<_>>(),
                        )
                        .with_node_limit(100);

                    let mini_egraph = runner.egraph;
                    if mini_egraph.find(l) == mini_egraph.find(r) {
                        // e1 and e2 are equivalent in the mini egraph
                        println!(
                            "skipping {e1} and {e2} because they are equivalent in the mini egraph"
                        );
                        continue;
                    }

                    candidates.add_from_recexprs(e1, e2);
                }
            }
        }
        candidates
    }

    pub fn select(&mut self, step_size: usize, invalid: &mut Ruleset<L>) -> Self {
        let mut chosen = Self::default();
        self.0
            .sort_by(|_, rule1, _, rule2| rule1.score().cmp(&rule2.score()));

        // 2. insert step_size best candidates into self.new_rws
        let mut selected: Ruleset<L> = Default::default();
        while selected.len() < step_size {
            let popped = self.0.pop();
            if let Some((_, rule)) = popped {
                if rule.is_valid() {
                    selected.add(rule.clone());
                } else {
                    invalid.add(rule.clone());
                }

                // If reverse direction is also in candidates, add it at the same time
                let reverse = if rule.cond.is_some() {
                    Rule::new_cond(&rule.rhs, &rule.lhs, &rule.cond.unwrap(), rule.true_count)
                } else {
                    Rule::new(&rule.rhs, &rule.lhs)
                };

                if let Some(reverse) = reverse {
                    if self.contains(&reverse) && reverse.is_valid() {
                        selected.add(reverse);
                    } else {
                        invalid.add(reverse);
                    }
                }
            } else {
                break;
            }
        }
        chosen.extend(selected);

        // 3. return chosen candidates
        chosen
    }

    fn shrink_cond(
        &mut self,
        chosen: &Self,
        prop_rules: &Vec<Rewrite<L, SynthAnalysis>>,
        most_recent_condition: &Assumption<L>,
    ) {
        let mut actual_by_cond: IndexMap<String, Ruleset<L>> = IndexMap::default();

        for (_, rule) in self.0.iter() {
            if let Some(cond) = &rule.cond {
                actual_by_cond
                    .entry(cond.chop_assumption().to_string())
                    .or_default()
                    .add(rule.clone());
            }
        }

        for (condition, _) in actual_by_cond.iter() {
            println!("condition: {condition:?}");
            let candidates = self
                .0
                .values()
                .filter(|rule| {
                    if let Some(cond) = &rule.cond {
                        cond.chop_assumption().to_string() == *condition
                    } else {
                        false
                    }
                })
                .collect::<Vec<_>>();

            println!("candidates:");
            for c in &candidates {
                println!("{c}");
            }

            // 1. Make a new e-graph.
            let mut egraph = EGraph::default();

            // 2. Add the condition of our candidates to the e-graph.
            let assumption: Assumption<L> = {
                let dummy: Assumption<L> = Assumption::new(condition.to_string()).unwrap();
                Assumption::new(L::instantiate(&dummy.chop_assumption()).to_string()).unwrap()
            };
            println!("adding {assumption} into the egraph");
            assumption.insert_into_egraph(&mut egraph);

            // 3. Add lhs, rhs of *all* candidates with the condition to the e-graph.
            let mut initial = vec![];
            for rule in candidates {
                // for rule in self.0.values() {
                let lhs = egraph.add_expr(&L::instantiate(&rule.lhs));
                let rhs = egraph.add_expr(&L::instantiate(&rule.rhs));
                initial.push((lhs, rhs, rule.clone()));
            }

            // 4. Run condition propagation rules, and the rewrites.
            let runner: Runner<L, SynthAnalysis> = Runner::default()
                .with_egraph(egraph.clone())
                .run(prop_rules)
                .with_node_limit(1000);

            let egraph = runner.egraph.clone();
            let egraph = Scheduler::Saturating(Limits {
                iter: 1,
                node: 100,
                match_: 1000,
            })
            .run(&egraph, chosen);

            // TODO: make this an optimization flag
            if most_recent_condition
                .chop_assumption()
                .search(&egraph)
                .is_empty()
            {
                println!("skipping {condition}");
                // if the most recent condition is not in the e-graph, then it's not relevant
                continue;
            }
            // 5. Compress the candidates with the rules we've chosen so far.
            // Anjali said this was good! Thank you Anjali!
            let scheduler = Scheduler::Saturating(Limits::deriving());
            let egraph = scheduler.run(&runner.egraph, chosen);

            // 6. For each candidate, see if the chosen rules have merged the lhs and rhs.
            for (l_id, r_id, rule) in initial {
                if egraph.find(l_id) == egraph.find(r_id) {
                    println!("condition: {condition}");
                    println!("removing rule {rule}");
                    let mut dummy: Ruleset<L> = Ruleset::default();
                    dummy.add(rule.clone());
                    self.remove_all(dummy.clone());
                } else {
                    println!("i'm keeping {rule}");
                }
            }
        }
    }

    fn shrink(&mut self, chosen: &Self, scheduler: Scheduler) {
        // 1. make new egraph
        // let mut egraph: EGraph<L, SynthAnalysis> = EGraph::default();
        let mut egraph = EGraph::default();

        let mut initial = vec![];
        // 2. insert lhs and rhs of all candidates as roots
        for rule in self.0.values() {
            let lhs = egraph.add_expr(&L::instantiate(&rule.lhs));
            let rhs = egraph.add_expr(&L::instantiate(&rule.rhs));
            initial.push((lhs, rhs, rule.clone()));
        }

        // 3. compress with the rules we've chosen so far
        let egraph = scheduler.run(&egraph, chosen);

        // 4. go through candidates and if they have merged, then
        // they are no longer candidates
        self.0 = Default::default();
        for (l_id, r_id, rule) in initial {
            if egraph.find(l_id) == egraph.find(r_id) {
                // candidate has merged (derivable from other rewrites)
                continue;
            } else {
                self.add(rule);
            }
        }
    }

    pub fn minimize_cond(
        &mut self,
        prior: Ruleset<L>,
        prop_rules: &Vec<Rewrite<L, SynthAnalysis>>,
    ) -> (Self, Self) {
        let start_time = std::time::Instant::now();
        println!(
            "[minimize_cond]: Minimizing {} rules with {} prior rules and {} prop rules",
            self.len(),
            prior.len(),
            prop_rules.len()
        );
        let mut invalid: Ruleset<L> = Default::default();
        let mut chosen = prior.clone();
        let step_size = 1;

        // bin the candidates by their conditions
        let mut by_cond: IndexMap<String, Ruleset<L>> = IndexMap::default();

        for rule in self.0.values() {
            if let Some(cond) = &rule.cond {
                by_cond
                    .entry(cond.clone().to_string())
                    .or_default()
                    .add(rule.clone());
            }
        }

        while !self.is_empty() {
            let selected = self.select(step_size, &mut invalid);
            if selected.is_empty() {
                continue;
            }

            // We might add `step_size` rules, and each rule might have a backwards version too.
            assert!(selected.len() <= step_size * 2);

            let most_recent_condition = &selected
                .0
                .values()
                .map(|rule| rule.cond.clone())
                .collect::<Vec<_>>()
                .first()
                .cloned()
                .unwrap()
                .unwrap();

            chosen.extend(selected.clone());

            self.shrink_cond(&chosen, prop_rules, most_recent_condition);
        }
        // Return only the new rules
        chosen.remove_all(prior);

        println!(
            "[minimize_cond] Kept {} new rules and found {} invalid rules in {} ms",
            chosen.len(),
            invalid.len(),
            start_time.elapsed().as_millis()
        );

        (chosen, invalid)
    }

    /// Minimization algorithm for rule selection
    ///     while there are still candidates to choose:
    ///         1. select the best rule candidate
    ///         2. filter out candidates that are redundant given the addition of the selected rule
    pub fn minimize(&mut self, prior: Ruleset<L>, scheduler: Scheduler) -> (Self, Self) {
        let start_time = std::time::Instant::now();
        println!(
            "[minimize] Minimizing {} rules with {} prior rules",
            self.len(),
            prior.len()
        );
        let mut invalid: Ruleset<L> = Default::default();
        let mut chosen = prior.clone();
        let step_size = 1;
        while !self.is_empty() {
            let selected = self.select(step_size, &mut invalid);
            chosen.extend(selected.clone());
            self.shrink(&chosen, scheduler);
        }
        // Return only the new rules
        chosen.remove_all(prior);

        println!(
            "[minimize] Kept {} new rules and found {} invalid rules in {} ms",
            chosen.len(),
            invalid.len(),
            start_time.elapsed().as_millis()
        );
        println!();

        (chosen, invalid)
    }

    /// Whether a given conditional rule can be derived by the ruleset with given resource limits
    ///     1. Initialize an e-graph with the rule (lhs => rhs) being tested.
    ///         If derive_type is Lhs, the e-graph is initialized with only lhs
    ///         If derive_type is LhsAndRhs, the e-graph is initialized with lhs and rhs
    ///     2. Add "TRUE" into the e-graph, and union it with the condition.
    ///     3. Run the condition propagation rules, i.e., set every condition which follows from
    ///        the given rule's condition to "TRUE".
    ///     4. Run the ruleset
    ///     5. Return true if the lhs and rhs are equivalent, false otherwise.
    pub fn can_derive_cond(
        &self,
        derive_type: DeriveType,
        rule: &Rule<L>,
        limits: Limits,
        condition_propagation_rules: &Vec<Rewrite<L, SynthAnalysis>>,
    ) -> bool {
        assert!(
            rule.cond.is_some(),
            "Rule must have a condition to derive conditionally"
        );
        let scheduler = Scheduler::Saturating(limits);
        let mut egraph: EGraph<L, SynthAnalysis> = EGraph::default();
        let lexpr = &L::instantiate(&rule.lhs);
        let rexpr = &L::instantiate(&rule.rhs);

        let condition = rule.cond.clone().unwrap();
        let cond = &L::instantiate(&condition.chop_assumption());

        egraph.add_expr(
            &format!("({} {})", L::assumption_label(), cond)
                .parse()
                .unwrap(),
        );
        // TODO: @ninehusky -- we can't use the API for a Scheduler to run the propagation rules
        // because they're not bundled in a Ruleset<L> anymore. I think this separation makes sense,
        // but maybe eventually we should just have a single Scheduler that can run both?

        // run the rules on the condition itself, for the tiniest smidge.
        let egraph = Scheduler::Saturating(Limits {
            iter: 2,
            node: 100,
            match_: 10_000,
        })
        .run(&egraph, self);
        let runner: Runner<L, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(condition_propagation_rules);

        let mut egraph = runner.egraph;

        let serialized = egg_to_serialized_egraph(&egraph);
        serialized.to_json_file("dump.json").unwrap();

        match derive_type {
            DeriveType::Lhs => {
                egraph.add_expr(lexpr);
            }
            DeriveType::LhsAndRhs => {
                egraph.add_expr(lexpr);
                egraph.add_expr(rexpr);
            }
        }

        let out_egraph = scheduler.run_derive(&egraph, self, rule);

        let l_id = out_egraph
            .lookup_expr(lexpr)
            .unwrap_or_else(|| panic!("Did not find {}", lexpr));
        let r_id = out_egraph.lookup_expr(rexpr);
        if let Some(r_id) = r_id {
            if l_id == r_id {
                // this should never happen.
                // this means that an `assume` node merged
                // with the lhs or rhs of the rule.
                assert_ne!(
                    out_egraph.number_of_classes(),
                    1,
                    "an assume node merged with somethin else!"
                );
            }
            l_id == r_id
        } else {
            false
        }
    }

    /// Whether a given rule can be derived by the ruleset with given resource limits
    ///     1. Initialize an e-graph with the rule (lhs => rhs) being tested.
    ///         If derive_type is Lhs, the e-graph is initialized with only lhs
    ///         If derive_type is LhsAndRhs, the e-graph is initialized with lhs and rhs
    ///     2. Run the ruleset
    ///     3. Return true if the lhs and rhs are equivalent, false otherwise.
    pub fn can_derive(&self, derive_type: DeriveType, rule: &Rule<L>, limits: Limits) -> bool {
        let scheduler = Scheduler::Saturating(limits);
        let mut egraph: EGraph<L, SynthAnalysis> = Default::default();
        let lexpr = &L::instantiate(&rule.lhs);
        let rexpr = &L::instantiate(&rule.rhs);

        match derive_type {
            DeriveType::Lhs => {
                egraph.add_expr(lexpr);
            }
            DeriveType::LhsAndRhs => {
                egraph.add_expr(lexpr);
                egraph.add_expr(rexpr);
            }
        }

        let out_egraph = scheduler.run_derive(&egraph, self, rule);

        let l_id = out_egraph
            .lookup_expr(lexpr)
            .unwrap_or_else(|| panic!("Did not find {}", lexpr));
        let r_id = out_egraph.lookup_expr(rexpr);
        if let Some(r_id) = r_id {
            l_id == r_id
        } else {
            false
        }
    }

    /// Partition a ruleset into derivable / not-derivable with respect to this ruleset.
    pub fn derive(
        &self,
        derive_type: DeriveType,
        against: &Self,
        limits: Limits,
        condition_propagation_rules: Option<&Vec<Rewrite<L, SynthAnalysis>>>,
    ) -> (Self, Self) {
        against.partition(|rule| {
            println!("attempting to derive: {}", rule.name);
            if rule.cond.is_some() {
                if condition_propagation_rules.is_none() {
                    panic!("Condition propagation rules required for conditional rules. You gave me: {:?}", rule);
                }
                self.can_derive_cond(
                    derive_type,
                    rule,
                    limits,
                    condition_propagation_rules.as_ref().unwrap(),
                )
            } else {
                self.can_derive(derive_type, rule, limits)
            }
        })
    }

    pub fn print_derive(derive_type: DeriveType, one: &str, two: &str) {
        let r1: Ruleset<L> = Ruleset::from_file(one);
        let r2: Ruleset<L> = Ruleset::from_file(two);

        let (_can, cannot) = r1.derive(derive_type, &r2, Limits::deriving(), None);
        {
            // std::io::_print(std::format_args_nl!(
            //     "Using {} ({}) to derive {} ({}).\nCan derive {}, cannot derive {}. Missing:",
            //     one,
            //     r1.len(),
            //     two,
            //     r2.len(),
            //     can.len(),
            //     cannot.len()
            // ));
        };
        cannot.pretty_print();
    }
}

pub fn egg_to_serialized_egraph<L, A>(egraph: &EGraph<L, A>) -> egraph_serialize::EGraph
where
    L: Language + Display,
    A: Analysis<L>,
{
    use egraph_serialize::*;
    let mut out = EGraph::default();
    for class in egraph.classes() {
        for (i, node) in class.nodes.iter().enumerate() {
            out.add_node(
                format!("{}.{}", class.id, i),
                Node {
                    op: node.to_string(),
                    children: node
                        .children()
                        .iter()
                        .map(|id| NodeId::from(format!("{id}.0")))
                        .collect(),
                    eclass: ClassId::from(format!("{}", class.id)),
                    cost: Cost::new(1.0).unwrap(),
                    subsumed: false,
                },
            )
        }
    }
    out
}

#[cfg(test)]
mod halide_tests {
    use crate::{conditions::implication::Implication, halide::Pred};

    use super::*;
    #[test]
    fn should_derive() {
        let mut existing_rules: Ruleset<Pred> = Default::default();
        existing_rules.add(Rule::from_string("(min ?a ?b) ==> (min ?b ?a)").unwrap().0);

        let mut candidates: Ruleset<Pred> = Default::default();
        candidates.add(
            Rule::from_string("(min ?a ?b) ==> ?b if (< ?b ?a)")
                .unwrap()
                .0,
        );
        candidates.add(
            Rule::from_string("(min ?a ?b) ==> ?a if (<= ?a ?b)")
                .unwrap()
                .0,
        );

        let mut implications: ImplicationSet<Pred> = Default::default();
        implications.add(
            Implication::new(
                "a < b -> a <= b".into(),
                "(< ?a ?b)".parse().unwrap(),
                "(<= ?a ?b)".parse().unwrap(),
            )
            .unwrap(),
        );

        let (chosen, _) = candidates.minimize_cond(existing_rules, &implications.to_egg_rewrites());
        assert_eq!(chosen.len(), 1);
    }
}

#[cfg(test)]
mod ruleset_tests {
    use crate::enumo::Workload;
    use crate::halide::Pred;
    use crate::{conditions::implication::Implication, enumo::ChompyState};

    use super::*;
    // In the egraph representing `(!= x 0)`, given the ruleset `R = {(/ ?x ?x) ==> 1 if (!= ?x 0)}`,
    // can we merge the e-classes of `(/ x x)` and `1`?
    #[test]
    fn test_construct_conditional_egraph_basic() {
        let mut black_egraph: EGraph<Pred, SynthAnalysis> = EGraph::default();

        black_egraph.add_expr(&"(/ x x)".parse().unwrap());
        black_egraph.add_expr(&"1".parse().unwrap());

        let predicate: Assumption<Pred> = "(!= x 0)".into();

        let mut prior: Ruleset<Pred> = Default::default();

        prior.add(Rule::from_string("(/ ?x ?x) ==> 1 if (!= ?x 0)").unwrap().0);

        let cond_egraph = Ruleset::construct_conditional_egraph(
            &black_egraph,
            &prior,
            &predicate,
            &Default::default(),
        );

        let l_id = cond_egraph
            .lookup_expr(&"(/ x x)".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find (/ x x)"));

        let r_id = cond_egraph
            .lookup_expr(&"1".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find 1"));

        assert_eq!(cond_egraph.find(l_id), cond_egraph.find(r_id));
    }

    // same thing as above, but with an additional step of condition implication.
    #[test]
    fn test_construct_conditional_egraph_advanced() {
        let mut black_egraph: EGraph<Pred, SynthAnalysis> = EGraph::default();

        black_egraph.add_expr(&"(/ x x)".parse().unwrap());
        black_egraph.add_expr(&"1".parse().unwrap());

        let predicate: Assumption<Pred> = "(< x 0)".into();

        let mut prior: Ruleset<Pred> = Default::default();

        prior.add(Rule::from_string("(/ ?x ?x) ==> 1 if (!= ?x 0)").unwrap().0);

        let mut implications: ImplicationSet<Pred> = Default::default();
        implications.add(
            Implication::new(
                "x < 0 -> x != 0".into(),
                "(< ?x 0)".parse().unwrap(),
                "(!= ?x 0)".parse().unwrap(),
            )
            .unwrap(),
        );

        let cond_egraph =
            Ruleset::construct_conditional_egraph(&black_egraph, &prior, &predicate, &implications);

        let l_id = cond_egraph
            .lookup_expr(&"(/ x x)".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find (/ x x)"));

        let r_id = cond_egraph
            .lookup_expr(&"1".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find 1"));

        assert_eq!(cond_egraph.find(l_id), cond_egraph.find(r_id));
    }

    // can we correctly identify a new conditional rule?
    #[test]
    fn get_canonical_conditional_rule_basic() {
        let mut egraph: EGraph<Pred, SynthAnalysis> = EGraph::default();
        egraph.add_expr(&"(+ (/ x x) (/ x x))".parse().unwrap());
        // we need to add the `(+ 1 1)` here because if we don't, then
        // the `Scheduler::Compress` won't be able to unify (+ (/ x x) (/ x x)) with (+ 1 1).
        egraph.add_expr(&"(+ 1 1)".parse().unwrap());
        egraph.add_expr(&"2".parse().unwrap());

        let predicate = "(!= x 0)".parse().unwrap();
        let mut prior: Ruleset<Pred> = Default::default();
        prior.add(Rule::from_string("(/ ?x ?x) ==> 1 if (!= ?x 0)").unwrap().0);

        let implications: ImplicationSet<Pred> = Default::default();

        // construct the conditional egraph
        let mini_egraph =
            Ruleset::construct_conditional_egraph(&egraph, &prior, &predicate, &implications);

        let result = Ruleset::get_canonical_conditional_rule(
            &"(+ (/ x x) (/ x x))".parse().unwrap(),
            &"2".parse().unwrap(),
            &predicate,
            &mini_egraph,
        );

        assert!(result.is_some());

        let (lhs, rhs) = result.unwrap();

        assert_eq!(
            lhs.to_string(),
            "(+ 1 1)".to_string(),
            "Expected lhs to be (+ 1 1), got {lhs}"
        );

        assert_eq!(
            rhs.to_string(),
            "2".to_string(),
            "Expected rhs to be 2, got {rhs}"
        );
    }

    // can we correctly filter out a redundant rule?
    #[test]
    fn get_canonical_conditional_rule_none() {
        let mut egraph: EGraph<Pred, SynthAnalysis> = EGraph::default();
        egraph.add_expr(&"(+ (/ x x) (/ x x))".parse().unwrap());
        // see `get_canonical_conditional_rule_basic` for why we need to add this `(+ 1 1)`.
        egraph.add_expr(&"(+ 1 1)".parse().unwrap());
        egraph.add_expr(&"2".parse().unwrap());

        let predicate = "(!= x 0)".parse().unwrap();
        let mut prior: Ruleset<Pred> = Default::default();
        prior.add(Rule::from_string("(/ ?x ?x) ==> 1 if (!= ?x 0)").unwrap().0);
        prior.add(Rule::from_string("(+ 1 1) ==> 2").unwrap().0);

        let implications: ImplicationSet<Pred> = Default::default();

        // construct the conditional egraph
        let mini_egraph =
            Ruleset::construct_conditional_egraph(&egraph, &prior, &predicate, &implications);

        let result = Ruleset::get_canonical_conditional_rule(
            &"(+ (/ x x) (/ x x))".parse().unwrap(),
            &"2".parse().unwrap(),
            &predicate,
            &mini_egraph,
        );

        assert!(result.is_none());
    }

    #[test]
    fn test_find_matching_conditions() {
        let term_egraph: EGraph<Pred, SynthAnalysis> = Workload::new(&["1", "(/ x x)"]).to_egraph();
        let one_id = term_egraph
            .lookup_expr(&"1".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find 1"));
        let x_div_x_id = term_egraph
            .lookup_expr(&"(/ x x)".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find (/ x x)"));
        let one_cvec = term_egraph[one_id].data.cvec.clone();
        let x_div_x_cvec = term_egraph[x_div_x_id].data.cvec.clone();

        let cond_egraph: EGraph<Pred, SynthAnalysis> =
            Workload::new(&["(< x 0)", "(!= x 0)", "(!= x 1)"]).to_egraph();

        let x_lt_zero = cond_egraph
            .lookup_expr(&"(< x 0)".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find (< x 0)"));
        let x_ne_zero = cond_egraph
            .lookup_expr(&"(!= x 0)".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find (!= x 0)"));
        let x_lt_zero_cvec = cond_egraph[x_lt_zero].data.cvec.clone();
        let x_ne_zero_cvec = cond_egraph[x_ne_zero].data.cvec.clone();
        let x_ne_one = cond_egraph
            .lookup_expr(&"(!= x 1)".parse().unwrap())
            .unwrap_or_else(|| panic!("Did not find (!= x 1)"));
        let x_ne_one_cvec = cond_egraph[x_ne_one].data.cvec.clone();

        let to_pvec = |cvec: &CVec<Pred>| -> PVec {
            cvec.iter()
                .map(|x| Pred::to_bool(x.unwrap_or(0)).unwrap())
                .collect::<Vec<bool>>()
        };

        let x_lt_zero_pvec = to_pvec(&x_lt_zero_cvec);
        let x_ne_zero_pvec = to_pvec(&x_ne_zero_cvec);
        let x_ne_one_pvec = to_pvec(&x_ne_one_cvec);

        let mut pvec_to_patterns: PredicateMap<Pred> = Default::default();
        pvec_to_patterns.insert(x_lt_zero_pvec, vec!["(< x 0)".parse().unwrap()]);
        pvec_to_patterns.insert(x_ne_zero_pvec, vec!["(!= x 0)".parse().unwrap()]);
        pvec_to_patterns.insert(x_ne_one_pvec, vec!["(!= x 1)".parse().unwrap()]);

        let conditions =
            Ruleset::<Pred>::find_matching_conditions(x_div_x_cvec, one_cvec, &pvec_to_patterns);

        assert_eq!(conditions.len(), 2);
        assert!(conditions.contains(&Assumption::from("(< x 0)")));
        assert!(conditions.contains(&Assumption::from("(!= x 0)")));
    }

    #[test]
    fn conditional_cvec_match_filter_redundant() {
        let state: ChompyState<Pred> = ChompyState::new(
            Workload::new(&["(/ x x)", "1"]),
            Ruleset::default(),
            Workload::new(&["(OP x 0)", "x"]).plug("OP", &Workload::new(&["<", "!="])),
            Default::default(),
        );

        let mut ruleset: Ruleset<Pred> = Default::default();
        ruleset.add(Rule::from_string("(/ ?x ?x) ==> 1 if (!= ?x 0)").unwrap().0);

        let candidates = Ruleset::conditional_cvec_match(
            &state.terms().to_egraph(),
            &ruleset,
            &state.pvec_to_patterns(),
            state.implications(),
        );

        assert!(candidates.is_empty());
    }

    // The above tests ensure that `conditional_cvec_match` correctly filters out candidates
    // that are already present in the ruleset.
    //
    // This test checks that it picks the weakest candidate when multiple candidates are available.
    #[test]
    fn conditional_cvec_match_picks_weakest() {
        let mut imps = ImplicationSet::default();
        imps.add(
            Implication::new(
                "?x < 0 -> ?x != 0".into(),
                "(< ?x 0)".parse().unwrap(),
                "(!= ?x 0)".parse().unwrap(),
            )
            .unwrap(),
        );

        imps.add(
            Implication::new(
                "?x > 0 -> ?x != 0".into(),
                "(> ?x 0)".parse().unwrap(),
                "(!= ?x 0)".parse().unwrap(),
            )
            .unwrap(),
        );

        let state = ChompyState::new(
            Workload::new(&["(/ x x)", "1"]),
            Ruleset::default(),
            Workload::new(&["(OP x 0)", "x"]).plug("OP", &Workload::new(&["<", "!=", ">"])),
            imps,
        );

        let candidates: Ruleset<Pred> = Ruleset::conditional_cvec_match(
            &state.terms().to_egraph(),
            &Ruleset::default(),
            &state.pvec_to_patterns(),
            state.implications(),
        );

        assert_eq!(candidates.len(), 1);
        assert!(candidates.contains(&Rule::from_string("(/ ?a ?a) ==> 1 if (!= ?a 0)").unwrap().0));
    }

    #[test]
    fn conditional_cvec_match_picks_weakest_renaming() {
        let mut imps = ImplicationSet::default();
        imps.add(
            Implication::new(
                "?x < 0 -> ?x != 0".into(),
                "(< ?x 0)".parse().unwrap(),
                "(!= ?x 0)".parse().unwrap(),
            )
            .unwrap(),
        );

        imps.add(
            Implication::new(
                "?x > 0 -> ?x != 0".into(),
                "(> ?x 0)".parse().unwrap(),
                "(!= ?x 0)".parse().unwrap(),
            )
            .unwrap(),
        );

        let state = ChompyState::new(
            Workload::new(&["(/ a (* a b))", "0"]),
            Ruleset::default(),
            Workload::new(&["(OP V 0)", "V"])
                .plug("OP", &Workload::new(&["=="]))
                .plug("V", &Workload::new(&["a", "b"])),
            imps,
        );

        let candidates: Ruleset<Pred> = Ruleset::conditional_cvec_match(
            &state.terms().to_egraph(),
            &Ruleset::default(),
            &state.pvec_to_patterns(),
            state.implications(),
        );

        for c in &candidates {
            println!("Candidate: {}", c.0);
        }

        assert!(candidates.contains(
            &Rule::from_string("(/ ?b (* ?b ?a)) ==> ?a if (== ?a 0)")
                .unwrap()
                .0
        ));
        assert!(candidates.contains(
            &Rule::from_string("(/ ?b (* ?b ?a)) ==> 0 if (== ?b 0)")
                .unwrap()
                .0
        ));
    }
}
