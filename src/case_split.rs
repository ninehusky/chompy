use crate::{
    conditions::{assumption::Assumption, implication_set::ImplicationSet},
    enumo::{Rule, Ruleset},
    halide::Pred,
    SynthAnalysis, SynthLanguage,
};
use egg::{EGraph, Pattern, Rewrite, Runner};

use std::collections::HashSet;

// ======== Split Records ========
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OrderSplit {
    lhs: String,
    rhs: String,
}

impl<L: SynthLanguage> From<OrderSplit> for Vec<Assumption<L>> {
    fn from(os: OrderSplit) -> Self {
        vec![
            Assumption::new(format!("(< {} {})", os.lhs, os.rhs)).unwrap(),
            Assumption::new(format!("(== {} {})", os.lhs, os.rhs)).unwrap(),
            Assumption::new(format!("(> {} {})", os.lhs, os.rhs)).unwrap(),
        ]
    }
}

#[derive(Clone, Debug)]
pub enum SplitCandidate {
    Order(OrderSplit),
}

// ======== CaseSplit Tracker ========
#[derive(Clone, Debug)]
struct CaseSplitTracker {
    done_order_splits: HashSet<OrderSplit>,
}

impl CaseSplitTracker {
    fn new() -> Self {
        Self {
            done_order_splits: HashSet::new(),
        }
    }

    // Generates candidate splits for a given rule
    fn get_next_split<L: SynthLanguage>(&mut self, rule: &Rule<L>) -> Option<SplitCandidate> {
        // TODO: does vars contain concrete variables or metavariables?
        let mut vars = rule.lhs.vars();
        vars.extend(rule.rhs.vars());

        let mut vars = vars
            .iter()
            .map(|v| {
                assert!(
                    v.to_string().starts_with('?'),
                    "Variable {} does not start with ?",
                    v
                );
                v.to_string().trim_start_matches('?').to_string()
            })
            .collect::<Vec<_>>();
        vars.sort();
        vars.dedup();

        for (i, v1) in vars.iter().enumerate() {
            for v2 in vars.iter().skip(i + 1) {
                if v1 == v2 {
                    continue;
                }

                let order_split = OrderSplit {
                    lhs: v1.to_string(),
                    rhs: v2.to_string(),
                };
                if !self.done_order_splits.contains(&order_split) {
                    self.done_order_splits.insert(order_split.clone());
                    return Some(SplitCandidate::Order(order_split));
                }
            }
        }
        None
    }
}

pub fn case_split_minimize<L: SynthLanguage>(
    ruleset: Ruleset<L>,
    initial: Ruleset<L>,
    implications: ImplicationSet<L>,
) -> Ruleset<L> {
    println!("Starting case splitting minimization...");
    println!("with {} implications", implications.len());

    let before_len = ruleset.len();
    let mut new_ruleset = initial.clone();
    let mut ruleset = ruleset.clone();
    while !ruleset.is_empty() {
        let chosen = ruleset.select(1, &mut Default::default());
        if chosen.is_empty() {
            break;
        }

        let (_, rule) = chosen.clone().into_iter().next().unwrap().clone();
        let result = !case_split(rule.clone(), new_ruleset.clone(), implications.clone());
        if result {
            new_ruleset.add(rule.clone());
        }
    }

    // Return only new rules
    // new_ruleset.remove_all(initial);

    // let final_len = new_ruleset.len();

    // println!("Finished case splitting minimization.");
    // println!(
    //     "Reduced ruleset from {} to {} rules ({} removed).",
    //     before_len,
    //     final_len,
    //     before_len - final_len
    // );

    new_ruleset
}

#[cfg(test)]
mod split_tests {
    use crate::{enumo::Rule, halide::Pred};

    use crate::case_split::SplitCandidate;

    #[test]
    fn test_order_split_from() {
        use super::*;
        let os = OrderSplit {
            lhs: "a".to_string(),
            rhs: "b".to_string(),
        };
        let assumptions: Vec<Assumption<Pred>> = os.clone().into();
        assert_eq!(assumptions.len(), 3);
        assert_eq!(assumptions[0].to_string(), "(assume (< a b))");
        assert_eq!(assumptions[1].to_string(), "(assume (== a b))");
        assert_eq!(assumptions[2].to_string(), "(assume (> a b))");
    }

    #[test]
    fn get_next_split_ok() {
        let rule: Rule<Pred> = Rule::from_string("(+ ?a ?b) ==> (+ ?b ?a)").unwrap().0;

        let mut tracker = super::CaseSplitTracker::new();
        let split = tracker.get_next_split(&rule);

        assert!(split.is_some());
        if let Some(SplitCandidate::Order(os)) = split {
            assert!((os.lhs == "a" && os.rhs == "b") || (os.lhs == "b" && os.rhs == "a"));
        } else {
            panic!("Expected Order split");
        }
    }

    #[test]
    fn get_next_split_none() {
        let rule: Rule<Pred> = Rule::from_string("(+ ?a ?b) ==> (+ ?a ?b)").unwrap().0;

        let mut tracker = super::CaseSplitTracker::new();
        let split = tracker.get_next_split(&rule);

        assert!(split.is_some());
        if let Some(SplitCandidate::Order(os)) = split {
            assert!((os.lhs == "a" && os.rhs == "b") || (os.lhs == "b" && os.rhs == "a"));
        } else {
            panic!("Expected Order split");
        }

        let next_split = tracker.get_next_split(&rule);
        assert!(next_split.is_none(), "Got: {:?}", next_split);
    }
}

// Returns false if you should keep it, true otherwise.
fn case_split<L: SynthLanguage>(
    rule: Rule<L>,
    ruleset: Ruleset<L>,
    implications: ImplicationSet<L>,
) -> bool {
    let tracker = CaseSplitTracker::new();
    println!("Case splitting on rule: {rule}");
    println!("My current rules:");
    for r in ruleset.iter() {
        println!("  {}", r);
    }
    case_split_internal(0, &rule, &[], &tracker, ruleset, implications)
}

fn is_false<L: SynthLanguage>(assumptions: &[Assumption<L>]) -> bool {
    // No assumptions means no contradiction
    if assumptions.is_empty() {
        return false;
    }
    // 1. Chop the "assume" keyword from each predicate
    // 2. And them all together
    // 3. Ask Z3 if the result is unsat
    // 4. If so, return true
    let patterns = assumptions
        .iter()
        .map(|a| a.chop_assumption())
        .collect::<Vec<Pattern<L>>>();

    let mut terms = String::new();
    fn construct_terms<L: SynthLanguage>(remaining: &[Pattern<L>], acc: &mut String) {
        if remaining.len() == 1 {
            acc.push_str(&remaining[0].to_string());
        } else if remaining.len() > 1 {
            acc.push_str("(&& ");
            acc.push_str(&remaining[0].to_string());
            construct_terms(&remaining[1..], acc);
            acc.push(')');
        }
    }

    construct_terms(&patterns, &mut terms);
    let rule: Rule<Pred> = Rule::from_string(&format!("{terms} ==> 0").to_string())
        .unwrap()
        .0;

    if rule.is_valid() {
        println!("Assumptions are contradictory: {terms}");
        true
    } else {
        false
    }
}

// Returns false if you should keep it. Returns true if you should throw it away.
fn case_split_internal<L: SynthLanguage>(
    depth: usize,
    rule: &Rule<L>,
    assumptions: &[Assumption<L>],
    tracker: &CaseSplitTracker,
    ruleset: Ruleset<L>,
    implications: ImplicationSet<L>,
) -> bool {
    if depth > 10 {
        println!("Bailed out of case splitting at depth {depth}");
        return false;
    }

    let assumptions: Vec<Assumption<L>> = if rule.cond.is_some() {
        let assumption_from_condition: Assumption<L> = Assumption::new(
            L::instantiate(&rule.cond.as_ref().unwrap().chop_assumption()).to_string(),
        )
        .expect("Failed to parse condition as assumption");
        [assumptions, &[assumption_from_condition]].concat()
    } else {
        assumptions.to_vec()
    };

    if is_false(assumptions.clone().as_slice()) {
        // We can vacuously prove anything in the world where false is true
        return true;
    }

    // actually, if we wanted, we could even cache this between calls.
    let mut egraph: EGraph<L, SynthAnalysis> = EGraph::default();
    let l_id = egraph.add_expr(&L::instantiate(&rule.lhs));
    let r_id = egraph.add_expr(&L::instantiate(&rule.rhs));

    // 1. add each assumption to the egraph.
    for a in assumptions.clone() {
        a.insert_into_egraph(&mut egraph);
    }

    let rules: Vec<Rewrite<L, SynthAnalysis>> = ruleset.iter().map(|r| r.rewrite.clone()).collect();

    // 2. rewrite the assumption as needed
    let runner: Runner<L, SynthAnalysis> = Runner::default().with_egraph(egraph).run(&rules);

    egraph = runner.egraph;

    // 3. run the implications that follow from the assumptions
    let runner: Runner<L, SynthAnalysis> = Runner::default()
        .with_egraph(egraph)
        .run(&implications.to_egg_rewrites());

    egraph = runner.egraph;

    // 4. rewrite the entire term space
    let runner: Runner<L, SynthAnalysis> = Runner::default().with_egraph(egraph).run(&rules);

    egraph = runner.egraph;

    if egraph.find(l_id) == egraph.find(r_id) {
        if depth == 0 {
            println!("Proved without case splits");
            // panic!("Proved without case splits!");
        }
        return true;
    }

    // 5. If this wasn't enough, get more assumptions
    let mut tracker = tracker.clone();
    if let Some(split) = tracker.get_next_split(rule) {
        match split {
            SplitCandidate::Order(o) => {
                let split_assumptions: Vec<Assumption<L>> = o.into();
                for a in &split_assumptions {
                    let new_assumptions = [assumptions.clone(), vec![a.clone()]].concat();
                    let result = case_split_internal(
                        depth + 1,
                        rule,
                        &new_assumptions,
                        &tracker,
                        ruleset.clone(),
                        implications.clone(),
                    );
                    if !result {
                        return false;
                    }
                    println!("Proved by case splitting at depth {depth}");
                }
            }
        }
    } else {
        println!("No more splits available at depth {depth}");
        return false;
    }

    true
}

#[cfg(test)]
pub mod analysis_tests {
    use crate::{
        case_split::case_split,
        enumo::{Filter, Metric, Rule, Ruleset, Workload},
        halide::Pred,
        recipe_utils::{base_lang, iter_metric, recursive_rules, run_workload, ChompyConfig, Lang},
        DeriveType, Limits,
    };

    #[test]
    pub fn see_craziness() {
        // 1. Just give me lemmas about min and + and <.
        let mut baseline: Ruleset<Pred> = recursive_rules(
            Metric::Atoms,
            9,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["+", "min"]]),
            Default::default(),
        );

        let lt_rules: Ruleset<Pred> = recursive_rules(
            Metric::Atoms,
            3,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["<"]]),
            Default::default(),
        );

        baseline.extend(lt_rules);
        baseline.add(
            Rule::from_string("(min ?a ?b) ==> ?a if (< ?a ?b)")
                .unwrap()
                .0,
        );

        let int_workload = iter_metric(base_lang(2), "EXPR", Metric::Atoms, 5)
            .filter(Filter::And(vec![
                Filter::Excludes("VAL".parse().unwrap()),
                Filter::Excludes("OP1".parse().unwrap()),
            ]))
            .plug("OP2", &Workload::new(&["min", "+"]))
            .plug("VAR", &Workload::new(&["a", "b", "c", "d"]));

        let lt_workload = Workload::new(&["(OP V V)", "0", "1"])
            .plug("OP", &Workload::new(&["<"]))
            .plug("V", &int_workload)
            .filter(Filter::Canon(vec![
                "a".to_string(),
                "b".to_string(),
                "c".to_string(),
                "d".to_string(),
            ]));

        // let cond_wkld =
        //     Workload::new(&["(< VAR 0)"]).plug("VAR", &Workload::new(&["a", "b", "c", "d"]));

        let minimized = run_workload(
            ChompyConfig::default()
                .with_workload(lt_workload.clone())
                .with_prior(baseline.clone())
                .with_case_split(true),
        );

        let full_rules = run_workload(
            ChompyConfig::default()
                .with_workload(lt_workload.clone())
                .with_prior(baseline.clone()),
        );

        let full_len = full_rules.len();
        println!("new rules (full):");
        full_rules.pretty_print();

        println!("new rules (case split):");
        minimized.pretty_print();

        println!(
            "Minimized {} to {} rules (difference of {})",
            full_len,
            minimized.len(),
            full_len - minimized.len()
        );
        minimized.pretty_print();

        for r in full_rules.iter() {
            if r.cond.is_some() {
                println!("Skipping conditional rule: {r}");
                continue;
            }
            assert!(
                case_split(r.clone(), minimized.clone(), Default::default()),
                "Failed to case split {}",
                r
            );
        }
    }
}
