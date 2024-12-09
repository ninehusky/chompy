use egglog::EGraph;
use ruler::enumo::{Filter, Metric, Pattern};
use ruler::{HashMap, HashSet, ValidationResult};
use utils::{TERM_PLACEHOLDER, UNIVERSAL_RELATION};

use std::fmt::Debug;
use std::hash::Hash;
use std::str::FromStr;

// use log::info;
use ruler::enumo::{Sexp, Workload};

pub mod ite;
pub mod utils;

pub type Constant<R> = <R as Chomper>::Constant;
pub type CVec<R> = Vec<Option<<R as Chomper>::Constant>>;
pub type Value<R> = <R as Chomper>::Value;

#[derive(Debug, PartialEq)]
pub struct Rule {
    // (condition, vector of environments under which subst_var(lhs, env) satisfies the condition)
    pub condition: Option<(Sexp, Vec<HashMap<String, Sexp>>)>,
    pub lhs: Sexp,
    pub rhs: Sexp,
}

pub struct Rules {
    pub non_conditional: Vec<Rule>,
    pub conditional: Vec<Rule>,
}

pub const MAX_SIZE: usize = 6;
pub const EXAMPLE_COUNT: usize = 1;

#[macro_export]
macro_rules! init_egraph {
    ($egraph:ident, $path:expr) => {
        $egraph
            .parse_and_run_program(Some($path.to_string()), include_str!($path))
            .unwrap();
    };
}
pub trait Chomper {
    type Constant: Debug + Clone + Eq + Hash;
    type Value: Debug + Clone + Eq + Hash;

    // stupid. see #2.
    fn make_string_not_bad(&self, term: &str) -> String {
        let mut term_string = term.to_string();
        for var in self.get_env().keys() {
            term_string = term_string.replace(&format!(" {} ", var), &format!(" \"{}\" ", var));
        }
        term_string
    }

    fn replace_vars(&self, term: &str) -> String {
        // separate term by whitespace.
        let tokens = term.split_whitespace().collect::<Vec<_>>();
        let mut result = String::new();
        for token in tokens {
            if token.starts_with("?") {
                result += format!(" \"{}\" ", token).as_str();
            } else {
                result += format!(" {token} ").as_str();
            }
        }
        result
    }

    fn make_mask_to_preds(&mut self) -> HashMap<Vec<bool>, HashSet<String>> {
        let mut result = HashMap::default();
        let preds = self.make_preds();
        for pred in preds.force() {
            let mask = self.interpret_pred(&pred);
            result
                .entry(mask)
                .or_insert(HashSet::default())
                .insert(pred.to_string());
        }
        result
    }

    fn run_chompy(&mut self, egraph: &mut EGraph) -> Vec<Rule> {
        // TODO: i want to use a set here.
        let mut found_rules: Vec<Rule> = vec![];
        let mut max_eclass_id = 0;

        let initial_egraph = egraph.clone();

        for current_size in 0..MAX_SIZE {
            println!("\n\nadding programs of size {}:", current_size);

            println!("finding eclass term map...");
            let eclass_term_map = self
                .reset_eclass_term_map(egraph)
                .values()
                .cloned()
                .collect::<Vec<_>>();
            let term_workload = Workload::new(
                eclass_term_map
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>(),
            );

            println!("eclasses len: {}", eclass_term_map.len());

            let new_workload = if term_workload.force().is_empty() {
                self.atoms().clone()
            } else {
                self.productions()
                    .clone()
                    .plug(TERM_PLACEHOLDER, &term_workload)
                    .filter(Filter::And(vec![
                        Filter::Canon(vec!["(Var a)".to_string(), "(Var b)".to_string()]),
                        Filter::MetricEq(Metric::Atoms, current_size),
                    ]))
            };

            println!("new workload len: {}", new_workload.force().len());

            let atoms = self.atoms().force();

            let memo = &mut HashSet::default();

            let mut seen_terms: HashSet<String> = HashSet::default();

            for term in &new_workload.force() {
                let generalized = self.generalize_sexp(term.clone());

                seen_terms.insert(generalized.to_string());

                let term_string = self.make_string_not_bad(term.to_string().as_str());

                if !atoms.contains(term) && !self.has_var(term) {
                    continue;
                }

                egraph
                    .parse_and_run_program(
                        None,
                        format!(
                            r#"
                        {term_string}
                        (set (eclass {term_string}) {max_eclass_id})
                        "#
                        )
                        .as_str(),
                    )
                    .unwrap();
                max_eclass_id += 1;
            }

            loop {
                println!("top of loop");
                println!("rules we've found: {}", found_rules.len());
                let serialized = egraph.serialize(egglog::SerializeConfig::default());
                println!("main egraph has {} nodes", serialized.nodes.len());
                egraph
                    .parse_and_run_program(
                        None,
                        r#"
                        (run non-cond-rewrites 1)
                        (run cond-rewrites 1)
                    "#,
                    )
                    .unwrap();

                let serialized = egraph.serialize(egglog::SerializeConfig::default());
                println!("main egraph has {} nodes", serialized.nodes.len());
                serialized
                    .to_svg_file(format!("egraph-{}.svg", current_size))
                    .unwrap();

                println!("starting cvec match");
                let vals = self.cvec_match(egraph, memo);

                if vals.non_conditional.is_empty() && vals.conditional.is_empty() {
                    break;
                }

                println!("found {} non-conditional rules", vals.non_conditional.len());
                println!("found {} conditional rules", vals.conditional.len());

                for val in &vals.conditional {
                    let generalized = self.generalize_rule(val);
                    if found_rules.contains(&generalized) {
                        continue;
                    }
                    if let ValidationResult::Valid = self.validate_rule(&generalized) {
                        if utils::does_rule_have_good_vars(&generalized) {
                            let rule = Rule {
                                condition: generalized.condition.clone(),
                                lhs: generalized.lhs.clone(),
                                rhs: generalized.rhs.clone(),
                            };
                            if !self.check_derivability(&initial_egraph, &found_rules, &generalized)
                            {
                                found_rules.push(rule);
                                egraph
                                    .parse_and_run_program(
                                        None,
                                        format!(
                                            r#"(cond-equal {} {})"#,
                                            self.make_string_not_bad(&val.lhs.to_string()).as_str(),
                                            self.make_string_not_bad(&val.rhs.to_string()).as_str()
                                        )
                                        .as_str(),
                                    )
                                    .unwrap();
                                self.add_conditional_rewrite(egraph, &generalized);
                                println!(
                                    "Conditional rule: if {} then {} ~> {}",
                                    generalized.condition.clone().unwrap().0,
                                    generalized.lhs,
                                    generalized.rhs
                                );
                            } else {
                                // println!(
                                //     "Derivability check failed. skipping if {} then {} ~> {}",
                                //     generalized.condition.clone().unwrap().0,
                                //     generalized.lhs,
                                //     generalized.rhs
                                // );
                            }
                        }
                    }
                }

                let mut new_rules: Vec<String> = vec![];
                for val in &vals.non_conditional {
                    let generalized = self.generalize_rule(val);
                    if let ValidationResult::Valid = self.validate_rule(&generalized) {
                        if utils::does_rule_have_good_vars(&generalized) {
                            let lhs =
                                self.make_string_not_bad(generalized.lhs.to_string().as_str());
                            let rhs =
                                self.make_string_not_bad(generalized.rhs.to_string().as_str());

                            if found_rules.contains(&generalized) {
                                continue;
                            }

                            if !self.check_derivability(&initial_egraph, &found_rules, &generalized)
                            {
                                let rule = Rule {
                                    condition: generalized.condition.clone(),
                                    lhs: generalized.lhs.clone(),
                                    rhs: generalized.rhs.clone(),
                                };
                                found_rules.push(rule);
                                println!("Rule: {} ~> {}", lhs, rhs);
                                self.add_rewrite(egraph, &generalized);
                                new_rules.push(format!("{} ~> {}", lhs, rhs));
                            } else {
                                // panic!("rule was derivable");
                            }
                        }
                    } else {
                        // println!(
                        //     "perfect cvec match but failed validation: {} ~> {}",
                        //     val.lhs, val.rhs
                        // );
                    }
                }

                if new_rules.is_empty() {
                    break;
                }
            }
        }

        // TODO: check
        found_rules
    }

    fn make_var(&self, var: &str) -> Sexp;
    fn make_constant(&self, constant: Constant<Self>) -> Sexp;
    fn get_name_from_var(&self, var: &Sexp) -> String;

    /// requires `env` to map placeholder variable identifiers (e.g., "?a") to
    /// specific, concrete values (i.e., not variables).
    fn concretize_term_conditional(&self, term: &Sexp, env: HashMap<String, Sexp>) -> Sexp {
        if self.matches_var_pattern(term) {
            let var_name = self.get_name_from_var(term);
            assert!(var_name.starts_with("?"));
            let var_name = var_name.trim_start_matches("?").to_string();
            if !env.contains_key(&var_name) {
                // TODO: check this
                // this might be a terrible idea.
                //
                return Sexp::from_str(&format!("(Lit 5)")).unwrap();
            }
            return env[&var_name].clone();
        }
        match term {
            Sexp::Atom(_) => term.clone(),
            Sexp::List(l) => Sexp::List(
                l.iter()
                    .map(|x| self.concretize_term_conditional(x, env.clone()))
                    .collect(),
            ),
        }
    }

    fn concretize_term(&self, term: &Sexp, env: &mut HashMap<String, Sexp>) -> Sexp {
        match term {
            Sexp::Atom(a) => {
                if !a.starts_with("?") {
                    return Sexp::Atom(a.clone());
                }
                let new_term = self.make_var(a);
                if env.contains_key(&a.clone()) {
                    return env[&a.clone()].clone();
                }
                env.insert(a.clone(), new_term.clone());
                new_term
            }
            Sexp::List(l) => Sexp::List(l.iter().map(|x| self.concretize_term(x, env)).collect()),
        }
    }

    fn concretize_rule(&self, rule: &Rule) -> (Sexp, Sexp) {
        // replace all variables with some arbitrary variable.
        let mut env = HashMap::default();
        let lhs = self.concretize_term(&rule.lhs, &mut env);
        let rhs = self.concretize_term(&rule.rhs, &mut env);
        (lhs, rhs)
    }

    // Returns if the rule is derivable; i.e., it shouldn't be added.
    fn check_derivability(
        &mut self,
        initial_egraph: &EGraph,
        ruleset: &Vec<Rule>,
        rule: &Rule,
    ) -> bool {
        println!("rules: {}", ruleset.len());
        // TODO: fix. return false;

        let mut initial_egraph = initial_egraph.clone();
        for rule in ruleset {
            if rule.condition.is_some() {
                self.add_conditional_rewrite(&mut initial_egraph, rule);
            } else {
                self.add_rewrite(&mut initial_egraph, rule);
            }
        }
        let (lhs, rhs) = self.concretize_rule(rule);
        match &rule.condition {
            Some((_, envs)) => {
                for env in envs {
                    println!("here is the env: {:?}", env);
                    println!("lhs: {}", lhs);
                    println!("rhs: {}", rhs);
                    let concretized_lhs = self.concretize_term_conditional(&lhs, env.clone());
                    let concretized_rhs = self.concretize_term_conditional(&rhs, env.clone());

                    let mut new_egraph = initial_egraph.clone();
                    new_egraph
                        .parse_and_run_program(
                            None,
                            format!(
                                r#"
                            (let lhs {})
                            (let rhs {})
                            ({UNIVERSAL_RELATION} {concretized_lhs})
                            ;;; ({UNIVERSAL_RELATION} {concretized_rhs})
                            "#,
                                concretized_lhs, concretized_rhs
                            )
                            .replace("quote", "\"")
                            .as_str(),
                        )
                        .unwrap();

                    new_egraph
                        .parse_and_run_program(
                            None,
                            r#"

                        (run non-cond-rewrites 10 :until (= lhs rhs))
                        (run cond-rewrites 10 :until (= lhs rhs))
                            ;;; (run non-cond-rewrites :until (= lhs rhs))
                            ;;; (run cond-rewrites :until (= lhs rhs))
                    "#,
                        )
                        .unwrap();

                    let serialized = new_egraph.serialize(egglog::SerializeConfig::default());
                    println!("eclasses: {}", serialized.root_eclasses.len());
                    println!("nodes: {}", serialized.nodes.len());

                    let result = new_egraph.parse_and_run_program(
                        None,
                        r#"
                        (check (= lhs rhs))
                    "#,
                    );

                    if result.is_err() {
                        // if for even a single environment, the lhs does not merge with the rhs,
                        // then the rule is underivable.
                        return false;
                    }
                }
                true
            }
            None => {
                initial_egraph
                    .parse_and_run_program(
                        None,
                        format!(
                            r#"
                            (let lhs {})
                            (let rhs {})
                    "#,
                            self.replace_vars(lhs.to_string().as_str()),
                            self.replace_vars(rhs.to_string().as_str())
                        )
                        .as_str(),
                    )
                    .unwrap();

                initial_egraph
                    .parse_and_run_program(
                        None,
                        r#"
                        (run non-cond-rewrites 10 :until (= lhs rhs))
                        ;;; uncommenting the line below will break things, because it will try to interpret variables.
                        ;;; (run cond-rewrites 3)
                    "#,
                    )
                    .unwrap();

                let serialized = initial_egraph.serialize(egglog::SerializeConfig::default());
                println!("eclasses: {}", serialized.root_eclasses.len());
                println!("nodes: {}", serialized.nodes.len());

                initial_egraph
                    .parse_and_run_program(
                        None,
                        r#"
                    (check (= lhs rhs))
                    "#,
                    )
                    .is_ok()
            }
        }
    }

    fn generalize_sexp(&self, sexp: Sexp) -> Sexp {
        if self.matches_var_pattern(&sexp) {
            let var_name = self.get_name_from_var(&sexp);
            return Sexp::Atom(format!("?{var_name}"));
        }
        match sexp {
            Sexp::Atom(atom) => Sexp::Atom(atom),
            Sexp::List(list) => {
                let mut els = vec![];
                for el in list {
                    els.push(self.generalize_sexp(el));
                }
                Sexp::List(els)
            }
        }
    }

    fn generalize_rule(&self, rule: &Rule) -> Rule {
        let new_lhs = self.generalize_sexp(rule.lhs.clone());
        let new_rhs = self.generalize_sexp(rule.rhs.clone());

        if rule.condition.is_none() {
            return Rule {
                condition: None,
                lhs: new_lhs,
                rhs: new_rhs,
            };
        }

        let condition = rule
            .condition
            .as_ref()
            .map(|cond| self.generalize_sexp(cond.clone().0));

        Rule {
            // TODO: later
            condition: Some((
                condition.unwrap(),
                rule.condition.as_ref().unwrap().1.clone(),
            )),
            lhs: new_lhs,
            rhs: new_rhs,
        }
    }

    fn reset_eclass_term_map(&self, egraph: &mut EGraph) -> HashMap<i64, Sexp> {
        let mut outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (push)
                (run eclass-report 100)
                (pop)"#,
            )
            .unwrap()
            .into_iter()
            .peekable();

        let mut map = HashMap::default();

        while outputs.peek().is_some() {
            outputs.next().unwrap();
            let eclass = outputs.next().unwrap().to_string().parse::<i64>().unwrap();
            outputs.next().unwrap();
            let term = outputs.next().unwrap();
            map.insert(eclass, Sexp::from_str(&term).unwrap());
        }
        map
    }

    fn cvec_match(
        &mut self,
        egraph: &mut EGraph,
        // keeps track of what eclass IDs we've seen.
        memo: &mut HashSet<i64>,
    ) -> Rules {
        let mut result = Rules {
            non_conditional: vec![],
            conditional: vec![],
        };

        let mask_to_preds = self.make_mask_to_preds();

        let eclass_term_map: HashMap<i64, Sexp> = self.reset_eclass_term_map(egraph);
        println!("eclass term map len: {}", eclass_term_map.len());
        let ec_keys: Vec<&i64> = eclass_term_map.keys().collect();
        for i in 0..ec_keys.len() {
            let ec1 = ec_keys[i];
            if memo.contains(ec1) {
                continue;
            }
            memo.insert(*ec1);
            let term1 = eclass_term_map.get(ec1).unwrap();
            let cvec1 = self.interpret_term(term1);
            if cvec1.iter().all(|x| x.is_none()) {
                // ignore cvecs which don't really matter
                continue;
            }
            for ec2 in ec_keys.iter().skip(i + 1) {
                let term2 = eclass_term_map.get(ec2).unwrap();

                let cvec2 = self.interpret_term(term2);

                if cvec2.iter().all(|x| x.is_none()) {
                    continue;
                }

                if cvec1 == cvec2 {
                    result.non_conditional.push(Rule {
                        condition: None,
                        lhs: term1.clone(),
                        rhs: term2.clone(),
                    });
                } else {
                    if egraph
                        .parse_and_run_program(
                            None,
                            format!("(check (cond-equal {term1} {term2}))").as_str(),
                        )
                        .is_ok()
                    {
                        println!(
                            "we already have a conditional rule for {}= {}",
                            term1, term2
                        );
                        // don't try to rederive some new way to link two e-classes together, if we
                        // already did it.
                        continue;
                    }

                    let mut has_meaningful_diff = false;
                    let mut same_vals: Vec<bool> = vec![];

                    let mut matching_count = 0;

                    for (cvec_1_el, cvec_2_el) in cvec1.iter().zip(cvec2.iter()) {
                        let has_match = cvec_1_el == cvec_2_el;
                        if has_match {
                            matching_count += 1;
                        }
                        if !has_match && cvec_1_el.is_some() || cvec_2_el.is_some() {
                            has_meaningful_diff = true;
                        }
                        same_vals.push(has_match);
                    }

                    if matching_count < 5 {
                        continue;
                    }
                    if !has_meaningful_diff {
                        println!("no meaningful diff");
                        continue;
                    }

                    // if the mask is all false, then skip it.
                    if same_vals.iter().all(|x| !x) {
                        continue;
                    }

                    // sufficient and necessary conditions.
                    if !mask_to_preds.contains_key(&same_vals) {
                        continue;
                    }
                    let preds = mask_to_preds.get(&same_vals).unwrap();
                    let global_env = self.get_env();
                    for pred in preds {
                        let mut envs: Vec<HashMap<String, Sexp>> = vec![];
                        // get the environment which satisfies the condition
                        for (i, val) in same_vals.iter().enumerate() {
                            // get at most EXAMPLE_COUNT environments
                            if envs.len() > EXAMPLE_COUNT {
                                break;
                            }
                            if !val {
                                continue;
                            }
                            let mut env: HashMap<String, Sexp> = HashMap::default();
                            for (variable, cvec) in global_env {
                                env.insert(
                                    variable.clone(),
                                    self.make_constant(cvec[i].as_ref().unwrap().clone()),
                                );
                            }
                            envs.push(env);
                        }

                        let rule = Rule {
                            condition: Some((Sexp::from_str(pred).unwrap(), envs)),
                            lhs: term1.clone(),
                            rhs: term2.clone(),
                        };
                        result.conditional.push(rule);
                    }
                }
            }
        }
        result
    }

    fn add_rewrite(&mut self, egraph: &mut EGraph, rule: &Rule) {
        let mut term1 = self.make_string_not_bad(rule.lhs.to_string().as_str());
        let mut term2 = self.make_string_not_bad(rule.rhs.to_string().as_str());
        // TODO: deal with rewrites which are essentially "anything matches this". they are not
        // good.
        if term1.len() == 2 {
            std::mem::swap(&mut term2, &mut term1);
        }

        let prog = format!(
            r#"
                    (rule
                     ({term1})
                     (
                        ({UNIVERSAL_RELATION} {term1})
                        ({UNIVERSAL_RELATION} {term2})
                        (union {term1} {term2})
                     )
                      :ruleset non-cond-rewrites)

                    ; (rewrite
                    ;     {term1}
                    ;     {term2}
                    ;     :ruleset non-cond-rewrites)
                    "#
        );

        egraph
            .parse_and_run_program(
                None,
                format!(
                    r#"
                    (rule
                     ({term1})
                     (({UNIVERSAL_RELATION} {term1})
                      ({UNIVERSAL_RELATION} {term2})
                      (union {term1} {term2}))
                      :ruleset non-cond-rewrites)

                    ; (rewrite
                    ;     {term1}
                    ;     {term2}
                    ;     :ruleset non-cond-rewrites)
                    "#
                )
                .as_str(),
            )
            .unwrap();
    }

    fn add_conditional_rewrite(&mut self, egraph: &mut EGraph, rule: &Rule) {
        // TODO: @ninehusky: let's brainstorm ways to encode conditional equality with respect to a
        // specific condition (see #20).
        let (cond, _) = rule.condition.as_ref().unwrap();
        let term1 = rule.lhs.to_string();
        let term2 = rule.rhs.to_string();

        let cond_rewrite_prog = format!(
            r#"
            (rule
                (({UNIVERSAL_RELATION} {term1}))

                (
                    (let temp (ite {cond} {term2} {term1}))
                    ({UNIVERSAL_RELATION} temp)
                    (union {term1} temp)
                )
                :ruleset cond-rewrites)
        "#
        );

        egraph
            .parse_and_run_program(None, &cond_rewrite_prog)
            .unwrap();
    }

    fn has_var(&self, term: &Sexp) -> bool {
        match term {
            Sexp::Atom(_) => self.matches_var_pattern(term),
            Sexp::List(list) => {
                for el in list {
                    if self.matches_var_pattern(el) || self.has_var(el) {
                        return true;
                    }
                }
                false
            }
        }
    }

    fn language_name() -> String;
    fn productions(&self) -> Workload;
    fn atoms(&self) -> Workload;
    fn make_preds(&self) -> Workload;
    fn get_env(&self) -> &HashMap<String, CVec<Self>>;
    fn validate_rule(&self, rule: &Rule) -> ValidationResult;
    fn interpret_term(&self, term: &ruler::enumo::Sexp) -> CVec<Self>;
    fn interpret_pred(&self, term: &ruler::enumo::Sexp) -> Vec<bool>;
    fn constant_pattern(&self) -> Pattern;
    fn matches_var_pattern(&self, term: &Sexp) -> bool;
}
