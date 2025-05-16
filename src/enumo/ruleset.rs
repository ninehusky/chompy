use egg::{Analysis, AstSize, EClass, Extractor, Language, Pattern, RecExpr, Rewrite, Runner};
use indexmap::map::{IntoIter, Iter, IterMut, Values, ValuesMut};
use rayon::iter::IntoParallelIterator;
use rayon::prelude::ParallelIterator;
use std::{fmt::Display, io::Write, str::FromStr, sync::Arc};

use crate::{
    halide::{self, Pred},
    recipe_utils::run_workload,
    CVec, DeriveType, EGraph, ExtractableAstSize, HashMap, Id, IndexMap, Limits, Signature,
    SynthAnalysis, SynthLanguage,
};

use super::{Rule, Scheduler, Workload};

const SACRED_RULE_NAME: &str = "(max ?b (+ ?b ?a)) ==> ?b if (<= ?a 0)";

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
                Rule::new_cond(&rule.rhs, &rule.lhs, &c)
            } else  {
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

    fn add_cond_from_recexprs(&mut self, e1: &RecExpr<L>, e2: &RecExpr<L>, cond: &RecExpr<L>) {
        let map = &mut HashMap::default();
        let l_pat = L::generalize(e1, map);
        let r_pat = L::generalize(e2, map);
        let cond_pat = L::generalize(cond, map);
        let forward = Rule::new_cond(&l_pat, &r_pat, &cond_pat);
        let backward = Rule::new_cond(&r_pat, &l_pat, &cond_pat);
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
            writeln!(file, "{}", name).expect("Unable to write");
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
                Rule::new_cond(&rule.rhs, &rule.lhs, &rule.cond.clone().unwrap())
            } else {
                Rule::new(&rule.rhs, &rule.lhs)
            };
            if reverse.is_some() && self.contains(&reverse.unwrap()) {
                let cond_display = if rule.cond.is_some() {
                    format!(" if {}", rule.cond.clone().unwrap())
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

    // TODO: @ninehusky: should this just be integrated into normal `cvec_match`?
    // See #5.
    pub fn conditional_cvec_match(
        egraph: &EGraph<L, SynthAnalysis>,
        conditions: &HashMap<Vec<bool>, Vec<Pattern<L>>>,
    ) -> Self {
        // // find (max a (+ b a)) in the egraph.
        // let max_id = egraph.lookup_expr(&"(max a (+ b a))".parse().unwrap());

        // if let Some(max_id) = max_id {
        //     // find the cvec for the max_id
        //     let max_cvec = egraph[max_id].data.cvec.clone();
        //     // find the cvec for "a"
        //     let a_id = egraph.lookup_expr(&"a".parse().unwrap()).unwrap();

        //     let a_cvec = egraph[a_id].data.cvec.clone();

        //     println!("max cvec: {:?}", max_cvec);
        //     println!("a cvec: {:?}", a_cvec);

        //     let pvec = max_cvec.iter().zip(a_cvec.iter()).map(|(a, b)| a == b).collect::<Vec<bool>>();

        //     println!("pvec: {:?}", pvec);

        //     let cond = conditions.get(&pvec);

        //     panic!("here is the condition matching (max a (+ b a)) and a: {:?}", cond);

        // }

        let mut by_cvec: IndexMap<&CVec<L>, Vec<Id>> = IndexMap::default();

        for class in egraph.classes() {
            if class.data.is_defined() {
                by_cvec.entry(&class.data.cvec).or_default().push(class.id);
            }
        }

        let mut candidates = Ruleset::default();
        let extract = Extractor::new(egraph, AstSize);

        let mut i = 0;
        for cvec1 in by_cvec.keys() {
            assert_eq!(cvec1.len(), conditions.keys().next().unwrap().len());
            i += 1;
            for cvec2 in by_cvec.keys().skip(i) {
                let pvec: Vec<bool> = cvec1
                    .iter()
                    .zip(cvec2.iter())
                    .map(|(a, b)| a == b)
                    .collect();

                if pvec.iter().all(|x| *x) || pvec.iter().all(|x| !*x) {
                    continue;
                }

                if let Some(pred_patterns) = conditions.get(&pvec) {
                    for pred_pat in pred_patterns {
                        for id1 in by_cvec[cvec1].clone() {
                            for id2 in by_cvec[cvec2].clone() {
                                let (c1, e1) = extract.find_best(id1);
                                let (c2, e2) = extract.find_best(id2);
                                let pred: RecExpr<L> =
                                    RecExpr::from_str(&pred_pat.to_string()).unwrap();
                                if c1 == usize::MAX || c2 == usize::MAX {
                                    continue;
                                }

                                // let max_id = egraph.lookup_expr(&"(max a (+ b a))".parse().unwrap());

                                // if let Some(max_id) = max_id {
                                //     // find the cvec for the max_id
                                //     let max_cvec = egraph[max_id].data.cvec.clone();
                                //     // find the cvec for "a"
                                //     let a_id = egraph.lookup_expr(&"a".parse().unwrap()).unwrap();
                                //     let a_cvec = egraph[a_id].data.cvec.clone();

                                //     if ((*cvec1).clone() == *a_cvec.clone() && (*cvec2).clone() == *max_cvec.clone()) ||
                                //         (*cvec1).clone() == *max_cvec.clone() && (*cvec2).clone() == *a_cvec.clone() {
                                //         println!("found a match for (max a (+ b a)) and a");
                                //         println!("candidate: if {} then {} ~> {}", pred, e1, e2);
                                //         // panic!();
                                //     }
                                // }

                                println!("candidate: if {} then {} ~> {}", pred, e1, e2);

                                candidates.add_cond_from_recexprs(&e1, &e2, &pred);
                            }
                        }
                    }
                }
            }
        }

        candidates
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
    pub fn fast_cvec_match(egraph: &EGraph<L, SynthAnalysis>) -> Ruleset<L> {
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
                    println!("{} is valid", rule.name);
                    selected.add(rule.clone());
                } else {
                    println!("{} is invalid", rule.name);
                    invalid.add(rule.clone());
                }

                // If reverse direction is also in candidates, add it at the same time
                let reverse = if rule.cond.is_some() {
                    Rule::new_cond(&rule.rhs, &rule.lhs, &rule.cond.unwrap())
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
        scheduler: Scheduler,
        prop_rules: &Vec<Rewrite<L, SynthAnalysis>>,
        by_cond: &IndexMap<String, Ruleset<L>>,
    ) {
        let mut actual_by_cond: IndexMap<String, Ruleset<L>> = IndexMap::default();

        for (rule_name, rule) in self.0.iter() {
            if let Some(cond) = &rule.cond {
                actual_by_cond
                    .entry(cond.clone().to_string())
                    .or_default()
                    .add(rule.clone());
            }
        }


        let mut should_remove = Ruleset::default();
        for (condition, candidates) in actual_by_cond.iter() {
            println!("condition: {}", condition);
            println!("candidates: {}", candidates.len());

            for c in candidates.iter() {
                println!("  {}", c.name);
            }


            let initial_len = candidates.len();
            let mut keep: Self = Default::default();
            // 1. Make a new e-graph.
            let mut egraph = EGraph::default();

            // 2. Add the condition to the e-graph.
            let cond_pat: &Pattern<L> = &condition.parse().unwrap();
            let cond_ast = &L::instantiate(cond_pat);
            egraph.add_expr(&format!("(istrue {})", cond_ast).parse().unwrap());

            // 3. Add lhs, rhs of all candidates with the condition to the e-graph.
            let mut initial = vec![];
            // for rule in self.0.values() {
            for (_, rule) in candidates {
                // // if the rule is no longer in the candidate ruleset (self), skip it.
                // if self.0.get(&rule.name).is_none() {
                //     continue;
                // }
                let lhs = egraph.add_expr(&L::instantiate(&rule.lhs));
                let rhs = egraph.add_expr(&L::instantiate(&rule.rhs));
                if rule.name == "(max ?b (+ ?b ?a)) ==> ?b if (<= ?a 0)".into() {
                    println!("adding in the sacred rule");
                }
                initial.push((lhs, rhs, rule.clone()));
            }

            // 4. Run condition propagation rules.
            let runner: Runner<L, SynthAnalysis> = Runner::default()
                .with_egraph(egraph.clone())
                .run(prop_rules);

            // println!("prop rules:");
            // for r in prop_rules {
            //     println!("  {}", r.name);
            // }

            // 5. Compress the candidates with the rules we've chosen so far.
            let egraph = scheduler.run(&runner.egraph, chosen);

            let mut removed = 0;

            // 6. For each candidate, see if the chosen rules have merged the lhs and rhs.
            for (l_id, r_id, rule) in initial {
                if egraph.find(l_id) == egraph.find(r_id) {
                    let r = Rule::<Pred>::from_string("(max ?b (+ ?b ?a)) ==> ?b if (<= ?a 0)");
                    assert!(r.unwrap().0.is_valid());
                    if rule.name == "(max ?b (+ ?b ?a)) ==> ?b if (<= ?a 0)".into() {
                        println!("should get here");
                    }
                    removed += 1;
                    should_remove.add(rule.clone());
                    continue;
                } else {
                    if rule.name == "(max ?b (+ ?b ?a)) ==> ?b if (<= ?a 0)".into() {
                        println!("we are keeping the sacred rule");
                    }

                    keep.add(rule);
                }
            }

            assert_eq!(keep.len(), initial_len - removed);
        }

        self.remove_all(should_remove.clone());
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
        scheduler: Scheduler,
        prop_rules: &Vec<Rewrite<L, SynthAnalysis>>,
    ) -> (Self, Self) {
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
            println!("candidates remaining: {}", self.len());
            let selected = self.select(step_size, &mut invalid);
            println!(
                "I have selected these: {:?}",
                selected.0.values().map(|rule| rule.name.clone()).collect::<Vec<_>>()
            );
            if selected.is_empty() {
                continue;
            }
            chosen.extend(selected.clone());

            let mut inside = false;
            for rule in self.0.values() {
                if rule.name == SACRED_RULE_NAME.into() {
                    inside = true;
                    println!("🟢 sacred rule is still in the pool");
                }
            }
            println!("now, calling shrink!");
            self.shrink_cond(&chosen, scheduler, prop_rules, &by_cond);
            let mut printed = false;
            for rule in self.0.values() {
                if rule.name == SACRED_RULE_NAME.into() {
                    printed = true;
                    println!("🟢 sacred rule is still in the pool");
                }
            }
            // if !printed && inside {
            //     panic!("sacred rule is not in the pool!");
            // }
        }
        // Return only the new rules
        chosen.remove_all(prior);

        (chosen, invalid)
    }

    /// Minimization algorithm for rule selection
    ///     while there are still candidates to choose:
    ///         1. select the best rule candidate
    ///         2. filter out candidates that are redundant given the addition of the selected rule
    pub fn minimize(&mut self, prior: Ruleset<L>, scheduler: Scheduler) -> (Self, Self) {
        let mut invalid: Ruleset<L> = Default::default();
        let mut chosen = prior.clone();
        let step_size = 1;
        while !self.is_empty() {
            let selected = self.select(step_size, &mut invalid);
            println!(
                "I have chosen: {}",
                selected.0.values().next().unwrap().name
            );
            // assert_eq!(selected.len(), 1); <-- wasn't this here in ruler?
            chosen.extend(selected.clone());
            self.shrink(&chosen, scheduler);
        }
        // Return only the new rules
        chosen.remove_all(prior);

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
        let scheduler = Scheduler::Saturating(limits);
        let mut egraph: EGraph<L, SynthAnalysis> = EGraph::default();
        let lexpr = &L::instantiate(&rule.lhs);
        let rexpr = &L::instantiate(&rule.rhs);

        let cond = &L::instantiate(&rule.cond.clone().unwrap());

        egraph.add_expr(&format!("(istrue {})", cond).parse().unwrap());

        match derive_type {
            DeriveType::Lhs => {
                egraph.add_expr(lexpr);
            }
            DeriveType::LhsAndRhs => {
                egraph.add_expr(lexpr);
                egraph.add_expr(rexpr);
            }
        }

        // TODO: @ninehusky -- we can't use the API for a Scheduler to run the propagation rules
        // because they're not bundled in a Ruleset<L> anymore. I think this separation makes sense,
        // but maybe eventually we should just have a single Scheduler that can run both?
        let runner: Runner<L, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(condition_propagation_rules);

        let egraph = runner.egraph;

        // println!("# eclasses in the egraph: {}", egraph.number_of_classes());

        // println!("cond: {}", cond);

        let out_egraph = scheduler.run_derive(&egraph, self, rule);

        // println!("lexpr: {}", lexpr);
        // println!("rexpr: {}", rexpr);

        // println!(
        //     "# eclasses in the egraph after rules: {}",
        //     out_egraph.number_of_classes()
        // );

        let serialized = egg_to_serialized_egraph(&out_egraph);

        // save it to egraph.json

        let mut file = std::fs::File::create("egraph.json")
            .unwrap_or_else(|_| panic!("Failed to open 'egraph.json'"));

        let serialized = serde_json::to_string_pretty(&serialized).unwrap();

        file.write_all(serialized.as_bytes())
            .expect("Unable to write");

        let l_id = out_egraph
            .lookup_expr(lexpr)
            .unwrap_or_else(|| panic!("Did not find {}", lexpr));
        let r_id = out_egraph.lookup_expr(rexpr);
        if let Some(r_id) = r_id {
            if l_id == r_id {
                // this should never happen.
                // this means that an `istrue` node merged
                // with the lhs or rhs of the rule.
                assert_ne!(
                    out_egraph.number_of_classes(),
                    1,
                    "an istrue node merged with somethin else!"
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
                        .map(|id| NodeId::from(format!("{}.0", id)))
                        .collect(),
                    subsumed: false,
                    eclass: ClassId::from(format!("{}", class.id)),
                    cost: Cost::new(1.0).unwrap(),
                },
            )
        }
    }
    out
}

// A series of tests containing some sanity checks about derivability.
pub mod tests {
    use crate::enumo::{rule, Rule};
    use crate::halide::Pred;
    use crate::ImplicationSwitch;

    use super::*;

    #[test]
    pub fn score_is_good() {
        let rule_1: Rule<Pred> = Rule::from_string("(min ?a (+ ?a ?a)) ==> (+ ?a ?a) if (<= ?a 0)")
            .unwrap()
            .0;

        let rule_2: Rule<Pred> = Rule::from_string("(+ ?a (max ?a ?b)) ==> (min ?a (+ ?a ?a)) if (&& (<= ?b ?a) (<= ?a 0))")
            .unwrap()
            .0;

        let r1_score = rule_1.score();
        let r2_score = rule_2.score();

        println!("{}: {:?}", rule_1, r1_score);
        println!("{}: {:?}", rule_2, r2_score);

        assert!(rule_1.score() < rule_2.score());

    }

    // R = {(min ?a ?b) <=> (min ?b ?a) (min (abs ?a) 0) ==> 0}.
    // r = (min 0 (abs ?a)) => 0.
    // test if R |= r.
    #[test]
    pub fn test_min_derive() {
        let mut ruleset: Ruleset<Pred> = Ruleset::default();
        let (fw, bw) = Rule::from_string("(min ?a ?b) <=> (min ?b ?a)").unwrap();
        ruleset.add(fw);
        ruleset.add(bw.unwrap());

        let (fw, _) = Rule::from_string("(min (abs ?a) 0) ==> 0").unwrap();

        ruleset.add(fw);

        let derivable = Rule::<Pred>::from_string("(min 0 (abs ?a)) ==> 0").unwrap();
        let mut derivable_rules = Ruleset::default();
        derivable_rules.add(derivable.0);

        let limits = Limits::deriving();
        let scheduler = Scheduler::Saturating(limits);

        derivable_rules.shrink(&ruleset, scheduler);
        assert_eq!(derivable_rules.len(), 0);
    }

    #[test]
    fn select_is_good() {
        let mut ruleset: Ruleset<Pred> = Ruleset::default();
        ruleset.add(
            Rule::from_string("(max ?b (+ ?b ?a)) ==> (min ?b ?a) if (&& (<= ?b ?a) (<= ?a 0))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(max ?b (+ ?b ?a)) ==> ?b if (&& (<= ?b ?a) (<= ?a 0))")
                .unwrap()
                .0,
        );


        let selected = ruleset.select(1, &mut Ruleset::default());
        let selected2 = ruleset.select(1, &mut Ruleset::default());
        println!("selected: {:?}", selected);
        println!("selected2: {:?}", selected2);
    }

    #[test]
    // R = {(max ?a ?b) <==> (max ?b ?a), if (<= ?a ?b) then (max ?a ?b) ==> ?b}
    // r = (max ?a ?b) ==> ?b if (<= ?a ?b).
    // test if R |= r.
    fn can_derive_simple() {
        let mut ruleset: Ruleset<Pred> = Ruleset::default();
        ruleset.add(Rule::from_string("(max ?a ?b) <=> (max ?b ?a)").unwrap().0);
        ruleset.add(
            Rule::from_string("(max ?a ?b) ==> ?b if (<= ?a ?b)")
                .unwrap()
                .0,
        );

        let term_wkld = Workload::new(&["(max a b)", "a"]);
        let cond_wkld = Workload::new(&["(<= a b)", "(<= b a)", "(>= a b)", "(>= b a)"]);

        let should_be_derivable: Rule<Pred> =
            Rule::from_string("(max ?a ?b) ==> ?a if (<= ?a ?b)").unwrap().0;
        assert!(should_be_derivable.is_valid());

        let (pvec_to_terms, implication_rules) =
            crate::conditions::generate::get_condition_propagation_rules_halide(&cond_wkld);

        let new_rules = run_workload(
            term_wkld,
            ruleset.clone(),
            Limits::synthesis(),
            Limits::synthesis(),
            true,
            Some(pvec_to_terms),
            Some(implication_rules),
        );

        // new rules are actually those that were not in the original ruleset
        let mut actual_new_rules = new_rules.clone();
        actual_new_rules.remove_all(ruleset);

        assert!(actual_new_rules.is_empty());

    }

    #[test]
    fn can_derive_4() {
        let mut ruleset: Ruleset<Pred> = Ruleset::default();
        ruleset.add(Rule::from_string("(max ?a ?b) <=> (max ?b ?a)").unwrap().0);
        ruleset.add(Rule::from_string("(min ?a ?b) <=> (min ?b ?a)").unwrap().0);
        ruleset.add(Rule::from_string("(+ ?a ?b) <=> (+ ?b ?a)").unwrap().0);

        ruleset.add(Rule::from_string("(min (max ?c ?b) (+ ?b ?a)) ==> (min (+ ?b ?a) (- ?b ?a)) if (<= ?a 0)").unwrap().0);

        let do_not_want = Rule::from_string("(min (+ ?b ?a) (max ?b ?c)) ==> (min (- ?b ?a) (+ ?b ?a)) if (<= ?a 0)").unwrap().0;

        let term_wkld = Workload::new(&["(min (+ b a) (max b c))", "(min (- b a) (+ b a))"]);
        let cond_wkld = Workload::new(&["(<= a 0)", "(<= b 0)", "(<= c 0)", "(<= a b)", "(<= b c)", "(<= c a)"]);

        let (pvec_to_terms, implication_rules) =
            crate::conditions::generate::get_condition_propagation_rules_halide(&cond_wkld);

        let new_rules = run_workload(
            term_wkld,
            ruleset.clone(),
            Limits::synthesis(),
            Limits::synthesis(),
            true,
            Some(pvec_to_terms),
            Some(implication_rules),
        );

        // new rules are actually those that were not in the original ruleset
        let mut actual_new_rules = new_rules.clone();

        actual_new_rules.remove_all(ruleset);

        assert!(!actual_new_rules.contains(&do_not_want));

    }

    #[test]
    fn can_derive_3() {
        let mut ruleset: Ruleset<Pred> = Ruleset::default();

        let term_wkld = Workload::new(&["(+ a (max b a))", "(min a (+ a a))", "a", "b", "(+ a a)", "(min a b)", "(min b a)", "(max a b)", "(max b a)"]);
        let cond_wkld = Workload::new(&["(&& (<= b a) (<= a 0))", "(<= a b)", "(>= a b)", "(<= b a)", "(>= b a)"]);

        // okay, so the new rules which should be synthesized given prior ruleset
        // and workloads are: NONE!

        let (pvec_to_terms, implication_rules) =
            crate::conditions::generate::get_condition_propagation_rules_halide(&cond_wkld);

        let mut additional_imps = implication_rules.clone();
        // (&& a b) ==> a
        additional_imps.push(
            ImplicationSwitch::new(&"(&& ?a ?b)".parse().unwrap(), &"?a".parse().unwrap())
                .rewrite(),
        );

        // (&& a b) ==> b
        additional_imps.push(
            ImplicationSwitch::new(&"(&& ?a ?b)".parse().unwrap(), &"?b".parse().unwrap())
                .rewrite(),
        );

        println!("implication rules:");
        for rule in additional_imps.iter() {
            println!("  {}", rule.name);
        }

        let new_rules = run_workload(
            term_wkld,
            ruleset.clone(),
            Limits::synthesis(),
            Limits::synthesis(),
            true,
            Some(pvec_to_terms),
            Some(additional_imps),
        );

        // new rules are actually those that were not in the original ruleset
        let mut actual_new_rules = new_rules.clone();
        actual_new_rules.remove_all(ruleset);

        assert!(actual_new_rules.is_empty());
    }

    #[test]
    fn can_derive_2() {
        let mut ruleset: Ruleset<Pred> = Ruleset::default();
        ruleset.add(Rule::from_string("(min ?a ?b) <=> (min ?b ?a)").unwrap().0);

        // we don't have this rule ruight now, but say we did.
        ruleset.add(
            Rule::from_string("(max ?b (+ ?b ?a)) ==> ?b if (&& (<= ?b ?a) (<= ?a 0))")
                .unwrap()
                .0,
        );

        assert!(Rule::<Pred>::from_string(
            "(max ?b (+ ?b ?a)) ==> ?b if (&& (<= ?b ?a) (<= ?a 0))"
        )
        .unwrap()
        .0
        .is_valid());

        let term_wkld = Workload::new(&["(max ?b (+ ?b ?a))", "(min ?b ?a)"]);
        let cond_wkld = Workload::new(&["(<= b a)", "(<= a 0)", "(&& (<= b a) (<= a 0))"]);

        let should_be_derivable: Rule<Pred> =
            Rule::from_string("(max ?b (+ ?b ?a)) ==> (min ?b ?a) if (&& (<= ?b ?a) (<= ?a 0))")
                .unwrap()
                .0;

        assert!(should_be_derivable.is_valid());

        let (pvec_to_terms, implication_rules) =
            crate::conditions::generate::get_condition_propagation_rules_halide(&cond_wkld);

        let mut additional_imps = implication_rules.clone();
        // (&& a b) ==> a
        additional_imps.push(
            ImplicationSwitch::new(&"(&& ?a ?b)".parse().unwrap(), &"?a".parse().unwrap())
                .rewrite(),
        );

        // (&& a b) ==> b
        additional_imps.push(
            ImplicationSwitch::new(&"(&& ?a ?b)".parse().unwrap(), &"?b".parse().unwrap())
                .rewrite(),
        );

        let new_rules = run_workload(
            term_wkld,
            ruleset.clone(),
            Limits::synthesis(),
            Limits::synthesis(),
            true,
            Some(pvec_to_terms),
            Some(additional_imps),
        );

        // new rules are actually those that were not in the original ruleset
        let mut actual_new_rules = new_rules.clone();
        actual_new_rules.remove_all(ruleset);

        assert!(actual_new_rules.is_empty());

        println!("new rules:");
        for rule in actual_new_rules.iter() {
            println!("{}", rule.name);
        }
    }

    #[test]
    fn can_derive_huh() {
        let mut ruleset: Ruleset<Pred> = Ruleset::default();
        ruleset.add(
            Rule::from_string("(max ?b (+ ?b ?a)) ==> ?b if (<= ?a 0)")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(max ?b (+ ?b ?a)) ==> (+ ?b ?a) if (>= ?a 0)")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(min ?a (+ ?a ?a)) ==> ?a if (>= ?a 0)")
                .unwrap()
                .0,
        );
        ruleset.add(Rule::from_string("(+ ?a ?b) ==> (+ ?b ?a)").unwrap().0);
        ruleset.add(Rule::from_string("(<= 0 ?b) ==> (>= ?b 0)").unwrap().0);

        let cond_wkld =
            Workload::new(&["(>= b 0)", "(>= a 0)", "(<= 0 b)", "(&& (<= a 0) (<= 0 b))"]);
        let test_wkld = Workload::new(&["(max b (+ b a))", "(min b (+ b b))"]);

        // the bug must be in the condition propagation rules: it should infer from:
        // a <= 0 and 0 <= b that:
        // a <= 0 ...
        // 0 <= b <--> b >= 0
        // using b >= 0, (min b (+ b b)) ==> b
        // using a <= 0, (max b (+ b a)) ==> b
        // and therefore, the rule (max b (+ b a)) ==> b should be derivable.
        // so the next step is to take a snapshot of the egraph after running the condition propagation rules
        // and asserting that if (istrue (&& (<= a 0) (<= 0 b))) is in the egraph, then
        // (istrue (<= a 0)) and (istrue (<= 0 b)) are also in the egraph.
        // orelse!

        let (pvec_to_terms, implication_rules) =
            crate::conditions::generate::get_condition_propagation_rules_halide(&cond_wkld);

        let mut additional_imps = implication_rules.clone();

        // (&& a b) ==> a
        additional_imps.push(
            ImplicationSwitch::new(&"(&& ?a ?b)".parse().unwrap(), &"?a".parse().unwrap())
                .rewrite(),
        );

        // (&& a b) ==> b
        additional_imps.push(
            ImplicationSwitch::new(&"(&& ?a ?b)".parse().unwrap(), &"?b".parse().unwrap())
                .rewrite(),
        );

        let new_rules = run_workload(
            test_wkld,
            ruleset.clone(),
            Limits::synthesis(),
            Limits::synthesis(),
            true,
            Some(pvec_to_terms),
            Some(additional_imps),
        );

        // new rules are actually those that were not in the original ruleset

        let mut actual_new_rules = new_rules.clone();

        actual_new_rules.remove_all(ruleset);

        println!("new rules:");

        for rule in actual_new_rules.iter() {
            println!("{}", rule.name);
        }
    }

    #[test]
    fn blah() {
        let cond_wkld = Workload::new(&["(&& (<= b 0) (<= 0 a))", "(&& (<= a 0) (<= 0 b))"]);
        // let term_wkld = Workload::new(&["(max a (+ b a))", "(max a (+ a a))", "a", "b"]);
        let term_wkld = Workload::new(&["(max b (+ b a))", "b"]);
        let (pvec_to_terms, implication_rules) =
            crate::conditions::generate::get_condition_propagation_rules_halide(&cond_wkld);

        println!("pvec_to_terms: {:?}", pvec_to_terms);
        println!("implication_rules: {:?}", implication_rules);

        let rules = run_workload(
            term_wkld,
            Ruleset::default(),
            Limits::synthesis(),
            Limits::synthesis(),
            true,
            Some(pvec_to_terms),
            Some(implication_rules),
        );

        println!("rules: {}", rules.to_str_vec().join("\n"));
    }
}
