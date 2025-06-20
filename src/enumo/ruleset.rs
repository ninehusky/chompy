use egg::{
    Analysis, AstSize, EClass, Extractor, Language, Pattern, RecExpr, Rewrite, Runner, Searcher,
};
use indexmap::map::{IntoIter, Iter, IterMut, Values, ValuesMut};
use rayon::iter::IntoParallelIterator;
use rayon::prelude::ParallelIterator;
use std::{fmt::Display, io::Write, str::FromStr, sync::Arc};

use crate::{
    conditions::merge_eqs,
    enumo::Sexp,
    halide::{self, Pred},
    recipe_utils::run_workload,
    CVec, DeriveType, EGraph, ExtractableAstSize, HashMap, Id, IndexMap, Limits, Signature,
    SynthAnalysis, SynthLanguage,
};

use super::{Rule, Scheduler, Workload};

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

    fn add_cond_from_recexprs(&mut self, e1: &RecExpr<L>, e2: &RecExpr<L>, cond: &RecExpr<L>) {
        println!("hi: {}", cond);
        let map = &mut HashMap::default();
        let l_pat = L::generalize(e1, map);
        let r_pat = L::generalize(e2, map);
        let cond_pat = L::generalize(cond, map);
        if e1.to_string() == "(/ a a)" && e2.to_string() == "1" {
            println!("div self!");
            println!("l_pat : {}", l_pat);
            println!("r_pat : {}", r_pat);
            println!("cond_pat: {}", cond_pat);
            panic!();
        }
        let forward = Rule::new_cond(&l_pat, &r_pat, &cond_pat);
        let backward = Rule::new_cond(&r_pat, &l_pat, &cond_pat);
        println!("forward: {:?}", forward);
        println!("backward: {:?}", backward);
        if let Some(forward) = forward {
            println!("adding forward rule: {}", forward.name);
            self.add(forward);
        }
        if let Some(backward) = backward {
            println!("adding backward rule: {}", backward.name);
            self.add(backward);
        }
        for (_, rule) in &self.0 {
            println!("rule: {}", rule.name);
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
        // find candidates with conditions of this size
        cond_size: usize,
        cond_to_egraph: &mut HashMap<String, EGraph<L, SynthAnalysis>>,
        prior: &Self,
        impl_rules: &Vec<Rewrite<L, SynthAnalysis>>,
    ) -> Self {
        println!("cond size: {}", cond_size);
        let mut by_cvec: IndexMap<&CVec<L>, Vec<Id>> = IndexMap::default();

        for class in egraph.classes() {
            if class.data.is_defined() {
                by_cvec.entry(&class.data.cvec).or_default().push(class.id);
            }
        }

        let conditional_rules: Ruleset<L> = prior.partition(|r| r.cond.is_some()).0;

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
                        let pred_string = pred_pat.to_string();
                        let cond_egraph =
                            cond_to_egraph
                                .entry(pred_string.clone())
                                .or_insert_with(|| {
                                    println!("inserting {:?}", pred_string); // this should only show on misses

                                    // this is the first part that might get ugly.
                                    let mut egraph = egraph.clone();

                                    // 2. add the condition to the egraph
                                    let cond_ast = &L::instantiate(pred_pat);

                                    println!("adding (assume {})", cond_ast);

                                    // 3. run the condition propagation rules
                                    egraph.add_expr(
                                        &format!("(assume {})", cond_ast).parse().unwrap(),
                                    );

                                    let runner: Runner<L, SynthAnalysis> =
                                        Runner::new(SynthAnalysis::default())
                                            .with_egraph(egraph.clone())
                                            .run(&impl_rules.clone())
                                            .with_node_limit(500);

                                    let egraph = runner.egraph;

                                    // 4. run the conditional rules for a snippet, given the ammo that we see above.
                                    //    this is the second part that might get ugly.
                                    let egraph = Scheduler::Saturating(Limits::deriving())
                                        .run(&egraph, &conditional_rules);

                                    egraph
                                });

                        // this is fucking stupid to do this here.
                        // if it gets expensive, we should do some pre-processing on the workload
                        // to make the upper-level data structure a map from usize -> map<pvec, patterns>
                        fn size(sexp: &Sexp) -> usize {
                            match sexp {
                                Sexp::Atom(_) => 1,
                                Sexp::List(list) => list.iter().map(size).sum(),
                            }
                        }

                        let size = size(&Sexp::from_str(&pred_pat.to_string()).unwrap());
                        if size != cond_size {
                            continue;
                        }

                        for id1 in by_cvec[cvec1].clone() {
                            for id2 in by_cvec[cvec2].clone() {
                                let (c1, e1) = extract.find_best(id1);
                                let (c2, e2) = extract.find_best(id2);
                                let pred: RecExpr<L> =
                                    RecExpr::from_str(&pred_pat.to_string()).unwrap();

                                fn size(sexp: &Sexp) -> usize {
                                    match sexp {
                                        Sexp::Atom(_) => 1,
                                        Sexp::List(list) => list.iter().map(size).sum(),
                                    }
                                }

                                let curr_size = size(&Sexp::from_str(&pred.to_string()).unwrap());

                                if curr_size != cond_size {
                                    // we're not looking for this condition size
                                    continue;
                                }

                                if c1 == usize::MAX || c2 == usize::MAX {
                                    continue;
                                }

                                // 1. get the e-graph with the implication rules already there
                                let egraph = &cond_egraph;

                                let lexpr = &L::instantiate(&e1.to_string().parse().unwrap());
                                let rexpr = &L::instantiate(&e2.to_string().parse().unwrap());

                                let l_id = egraph
                                    .lookup_expr(lexpr)
                                    .unwrap_or_else(|| panic!("Did not find {}", lexpr));

                                let r_id = egraph
                                    .lookup_expr(rexpr)
                                    .unwrap_or_else(|| panic!("Did not find {}", rexpr));

                                // 2. check if the lhs and rhs are equivalent in the egraph
                                if l_id == r_id {
                                    // e1 and e2 are equivalent in the condition egraph
                                    println!(
                                        "Skipping {} and {} because they are equivalent in the egraph representing {}",
                                        e1, e2, pred_pat
                                    );
                                    continue;
                                }
                                // END HACK

                                println!("adding: if {} then {} ~> {}", pred_pat, e1, e2);
                                candidates.add_cond_from_recexprs(&e1, &e2, &pred);
                                println!("candidates len: {}", candidates.len());
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
                    println!("candidate: {} ~> {}", e1, e2);
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
        most_recent_condition: &Pattern<L>,
    ) {
        let mut actual_by_cond: IndexMap<String, Ruleset<L>> = IndexMap::default();

        for (_, rule) in self.0.iter() {
            if let Some(cond) = &rule.cond {
                actual_by_cond
                    .entry(cond.clone().to_string())
                    .or_default()
                    .add(rule.clone());
            }
        }

        for (condition, _) in actual_by_cond.iter() {
            let candidates = self
                .0
                .values()
                .filter(|rule| {
                    if let Some(cond) = &rule.cond {
                        cond.to_string() == condition.to_string()
                    } else {
                        false
                    }
                })
                .collect::<Vec<_>>();

            // 1. Make a new e-graph.
            let mut egraph = EGraph::default();

            // 2. Add the condition to the e-graph.
            let cond_pat: &Pattern<L> = &condition.parse().unwrap();
            let cond_ast = &L::instantiate(cond_pat);
            println!("adding {}", cond_ast);
            egraph.add_expr(&format!("(assume {})", cond_ast).parse().unwrap());

            // 3. Add lhs, rhs of *all* candidates with the condition to the e-graph.
            let mut initial = vec![];
            for rule in candidates {
                // for rule in self.0.values() {
                let lhs = egraph.add_expr(&L::instantiate(&rule.lhs));
                let rhs = egraph.add_expr(&L::instantiate(&rule.rhs));
                initial.push((lhs, rhs, rule.clone()));
            }

            // 4. Run condition propagation rules.
            let runner: Runner<L, SynthAnalysis> = Runner::default()
                .with_egraph(egraph.clone())
                .run(prop_rules)
                .with_node_limit(500);

            let egraph = runner.egraph.clone();

            // see if the most recently added condition is in the e-graph.
            if most_recent_condition.search(&egraph).is_empty() {
                println!(
                    "most recent condition {} is not in the egraph representing {}, so skipping.",
                    most_recent_condition, condition
                );
                if most_recent_condition.to_string() == condition.to_string() {
                    // dump e-graph to json.
                    let serialized = egg_to_serialized_egraph(&egraph);
                    serialized.to_json_file("uhoh.json");
                    panic!();
                }
                // then it's not relevant
                continue;
            }

            // 5. Compress the candidates with the rules we've chosen so far.
            // Anjali said this was good! Thank you Anjali!
            let scheduler = Scheduler::Compress(Limits::deriving());
            println!("chosen: ");
            for rule in chosen.0.values() {
                println!("  {}: {}", rule.name, rule.lhs);
            }
            let egraph = scheduler.run(&runner.egraph, &chosen);

            // 6. For each candidate, see if the chosen rules have merged the lhs and rhs.
            for (l_id, r_id, rule) in initial {
                println!("seeing if we can derive this rule: {}", rule.name);
                if egraph.find(l_id) == egraph.find(r_id) {
                    let mut dummy: Ruleset<L> = Ruleset::default();
                    dummy.add(rule.clone());
                    println!("removing {}", rule.name);
                    self.remove_all(dummy.clone());
                } else {
                    println!("keeping {}", rule.name);
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
            if selected.is_empty() {
                continue;
            }

            assert_eq!(selected.len(), 1);

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

            println!("now, calling shrink!");
            self.shrink_cond(
                &chosen,
                scheduler,
                prop_rules,
                &by_cond,
                most_recent_condition,
            );
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

        egraph.add_expr(&format!("(assume {})", cond).parse().unwrap());

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

#[cfg(test)]
pub mod cond_cvec_match_tests {
    use egg::{AstSize, EGraph, Extractor, Pattern};

    use crate::{enumo::{Ruleset, Workload}, HashMap, PVec, SynthAnalysis, SynthLanguage};

    // Cond cvec matching should find the candidate (/ a a) ~> 1 if (!= a 0).
    #[test]
    fn cond_cvec_match_sanity_div_self() {
        // use crate::enumo::{rule, scheduler, workload, Rule};
        // use crate::halide::{compute_conditional_structures, Pred};
        // use crate::ImplicationSwitch;

        // let workload = Workload::new(&["(/ a a)"]);
        // let mut egraph = workload.to_egraph();

        // let mut pvec_to_patterns: HashMap<Vec<bool>, Vec<Pattern<Pred>>> = HashMap::default();

        // let cond_egraph: EGraph<Pred, SynthAnalysis> = Workload::new(&["(!= a 0)"]).to_egraph();
        // let extractor = Extractor::new(&cond_egraph, AstSize);

        // for c in cond_egraph.classes() {
        //     let pat = Pred::generalize(&extractor.find_best(c.id).1, &mut Default::default());
        //     if !Pred::pattern_is_predicate(&pat) {
        //         continue;
        //     }

        //     let pvec = c
        //         .data
        //         .cvec
        //         .iter()
        //         .map(|x| {
        //             if let Some(p) = x.as_ref() {
        //                 Pred::to_bool(p.clone()).unwrap()
        //             } else {
        //                 false
        //             }
        //         })
        //         .collect::<PVec>();

        //     pvec_to_patterns
        //         .entry(pvec.clone())
        //         .or_default()
        //         .push(pat.clone());
        // }

    }
}

// A series of tests containing some sanity checks about derivability.
pub mod tests {
    use crate::enumo::{rule, scheduler, workload, Rule};
    use crate::halide::{compute_conditional_structures, Pred};
    use crate::ImplicationSwitch;

    use super::*;

    #[test]
    pub fn ugh() {
        let mut rules = Ruleset::default();
        let rule: Rule<Pred> = Rule::from_string("(max ?a ?b) <=> (max ?b ?a)").unwrap().0;
        let dummy: Rule<Pred> = Rule::from_string("(+ ?a (- ?b)) ==> (- ?a ?b)").unwrap().0;
        let dummy: Rule<Pred> = Rule::from_string("(/ (* -1 ?a) ?b) ==> (* -1 (/ ?a ?b))")
            .unwrap()
            .0;
        assert!(dummy.is_valid());
        rules.add(rule);

        let scheduler = scheduler::Scheduler::Saturating(Limits::minimize());

        let mut egraph: EGraph<Pred, SynthAnalysis> = EGraph::default();
        egraph.add_expr(&"(max a b)".parse().unwrap());
        // egraph.add_expr(&"(max b a)".parse().unwrap());

        let egraph = scheduler.run(&egraph, &rules);
        assert!(
            egraph.lookup_expr(&"(max a b)".parse().unwrap())
                == egraph.lookup_expr(&"(max b a)".parse().unwrap())
        );
    }

    #[test]
    pub fn condition_fires() {
        let rule: Rule<Pred> = Rule::from_string("(max ?a ?b) ==> ?a if (<= ?b ?a)")
            .unwrap()
            .0;
        let rule2: Rule<Pred> = Rule::from_string("(max ?a ?b) <=> (max ?b ?a)").unwrap().0;
        let mut ruleset = Ruleset::default();
        ruleset.add(rule);
        ruleset.add(rule2);

        let scheduler = scheduler::Scheduler::Compress(Limits::deriving());

        let mut egraph: EGraph<Pred, SynthAnalysis> = EGraph::default();
        let og_id = egraph.add_expr(&"(max a b)".parse().unwrap());
        egraph.add_expr(&"(assume (<= a b))".parse().unwrap());

        let egraph = scheduler.run(&egraph, &ruleset);

        let extractor = Extractor::new(&egraph, AstSize);

        let (_, best_expr) = extractor.find_best(og_id);
        println!("{}", best_expr);
    }

    #[test]
    pub fn score_is_good() {
        let rule_1: Rule<Pred> = Rule::from_string("(min ?a (+ ?a ?a)) ==> (+ ?a ?a) if (<= ?a 0)")
            .unwrap()
            .0;

        let rule_2: Rule<Pred> = Rule::from_string(
            "(+ ?a (max ?a ?b)) ==> (min ?a (+ ?a ?a)) if (&& (<= ?b ?a) (<= ?a 0))",
        )
        .unwrap()
        .0;

        let mut ruleset = Ruleset::default();
        ruleset.add(rule_1.clone());
        ruleset.add(rule_2.clone());

        let mut expected = Ruleset::default();
        expected.add(rule_1.clone());

        assert_eq!(ruleset.select(1, &mut Ruleset::default()), expected);
    }

    #[test]
    pub fn score_is_good_2() {
        let mut ruleset: Ruleset<Pred> = Ruleset::default();
        ruleset.add(
            Rule::from_string("(/ ?b ?a) ==> 1 if (&& (!= ?b 0) (== ?b ?a))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(/ ?b ?a) ==> 1 if (&& (!= ?a 0) (== ?a ?b))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(- ?b ?a) ==> (+ ?b ?b) if (== 0 (+ ?b ?a))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(/ ?a ?b) ==> (+ ?a ?a) if (== ?b (+ ?b ?a))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(- ?b ?a) ==> (- ?b) if (== ?b (- ?a ?b))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(- ?b ?a) ==> (- ?b) if (== ?a (+ ?b ?b))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(- ?b ?a) ==> (- ?a) if (== ?a (+ ?a ?b))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(- ?a ?b) ==> ?a if (== ?a (+ ?a ?b))")
                .unwrap()
                .0,
        );
        ruleset.add(
            Rule::from_string("(- ?b ?a) ==> ?a if (== ?b (+ ?a ?a))")
                .unwrap()
                .0,
        );
        ruleset.add(Rule::from_string("(/ ?a ?a) ==> 1 if (!= ?a 0)").unwrap().0);

        let mut names = vec![];

        while !ruleset.is_empty() {
            let selected = ruleset.select(1, &mut Ruleset::default());
            if selected.is_empty() {
                break;
            }
            for (_, rule) in selected.0.iter() {
                println!("  {}", rule.name);
                names.push(rule.name.clone());
            }
            ruleset.remove_all(selected);
        }
        println!("selected rules: {:?}", names);
    }

    #[test]
    #[test]
    // A test for optimization 2.
    // Given the rules: `[(+ 0 1) ==> 1, (/ ?a ?a) ==> 1 if (!= ?a 0)]``,
    // will the candidate (+ 0 (/ ?a ?a)) ==> 1 if (!= ?a 0) get chosen?
    pub fn conditional_cvec_match_filters() {
        // the bare minimum to get the above rule as a candidate.
        let workload = Workload::new(&["1", "(+ 0 (/ a a))"]);

        let condition = Workload::new(&["(!= a 0)"]);

        let (cond_map, mut impl_rules) = compute_conditional_structures(&condition);
        impl_rules.push(merge_eqs());

        assert_eq!(impl_rules.len(), 1);
        assert_eq!(cond_map.len(), 1);

        let mut prior: Ruleset<Pred> = Ruleset::default();
        prior.add(Rule::from_string("(/ ?a ?a) ==> 1 if (!= ?a 0)").unwrap().0);
        prior.add(Rule::from_string("(+ 0 1) ==> 1").unwrap().0);

        let egraph: EGraph<Pred, SynthAnalysis> = workload.to_egraph();

        let candidates: Ruleset<Pred> = Ruleset::conditional_cvec_match(
            &egraph,
            &cond_map,
            8,
            &mut Default::default(),
            &prior,
            &impl_rules,
        );

        // no candidates should have been discovered.
        // in the world where (assume (!= a 0)), (/ a a) ==> 1.
        // thus (+ 0 1) ==> 1 will fire.
        println!("candidates:");
        for c in candidates.clone() {
            println!("   {}", c.1.name);
        }

        assert!(candidates.is_empty());
    }

    #[test]
    // Another test for optimization 2.
    // `(- 1 (* ?b ?a)) ==> (/ ?a ?a) if (&& (== ?b 0) (!= ?b ?a))`
    // This rule should be derived from the following rules:
    // `[(- 1 0) ==> 1, (/ ?a ?a) ==> 1 if (!= ?a 0)]`
    pub fn conditional_cvec_match_filters_complex() {
        let workload = Workload::new(&["(/ a a)", "(- 1 (* b a))"]);
        let conditions =
            Workload::new(&["(== b 0)", "(!= b a)", "(&& (== b 0) (!= b a))", "(!= a 0)"]);

        let (cond_map, mut impl_rules) = compute_conditional_structures(&conditions);
        impl_rules.push(merge_eqs());

        println!("impl_rules: {:?}", impl_rules);

        let mut prior: Ruleset<Pred> = Ruleset::default();
        prior.add(Rule::from_string("(/ ?a ?a) ==> 1 if (!= ?a 0)").unwrap().0);
        prior.add(Rule::from_string("(- ?a 0) ==> ?a").unwrap().0);
        prior.add(Rule::from_string("(* 0 ?a) ==> 0").unwrap().0);

        let egraph: EGraph<Pred, SynthAnalysis> = workload.to_egraph();

        let candidates: Ruleset<Pred> = Ruleset::conditional_cvec_match(
            &egraph,
            &cond_map,
            8,
            &mut Default::default(),
            &prior,
            &impl_rules,
        );

        // no candidates should have been discovered.
        assert!(candidates.is_empty());
    }

    // given (min ?a ?b) <=> (min ?b ?a), only derive one of [(min ?a ?b) ==> ?a if (<= ?a ?b), (min ?b ?a) ==> ?a if (<= ?a ?b)].
    #[test]
    fn basic_derive() {
        // let mut ruleset = Ruleset::default();
        // ruleset.add(Rule::from_string("(min ?a ?b) <=> (min ?b ?a)").unwrap().0);

        // let term_workload = Workload::new(&["(min a b)", "(min b a)"]);
        // let cond_workload = Workload::new(&["(<= a b)"]);

        // let (pvec_to_patterns, prop_rules) = compute_conditional_structures(&cond_workload);

        // let found = run_workload(
        //     term_workload,
        //     ruleset,
        //     Limits::synthesis(),
        //     Limits::minimize(),
        //     true,
        //     Some(pvec_to_patterns),
        //     Some(prop_rules),
        // );

        // for r in found {
        //     println!("found: {}", r.0);
        // }
    }
}
