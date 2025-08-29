use egg::{EGraph, Pattern, Rewrite, Runner, Var};
use ruler::{conditions::{assumption::Assumption, implication_set::ImplicationSet}, enumo::{Rule, Ruleset}, halide::Pred, SynthAnalysis, SynthLanguage};

// We'll implement the below function shortly.
// // Return false if the rule is NOT derivable by case splitting (keep the rule).
// // Return true if the rule is derivable by case splitting (ditch it).
// fn case_split_internal(depth, rule, assumptions, ruleset, imps) -> bool {
//    if depth > MAX_DEPTH:
//       return false

//    // We can vacuously prove anything in the world where false is true
//    if assumptions.union() == false {
//       return true
//    }

//    egraph = new_egraph()
//    l_id = egraph.add_expr(rule.lhs)
//    r_id = egraph.add_expr(rule.rhs)

//    // 1. add each assumption to the egraph.
//    for a in assumptions:
//        a.insert_into_egraph(egraph)

//    // 2. rewrite the assumption as needed
//    egraph.run_rules(ruleset)

//    // 3. run the implications that follow from the assumptions
//    egraph.run_implications(imps)

//    // 4. rewrite the entire term space
//    egraph.run_rules(ruleset)

//    if egraph.find(l_id) == egraph.find(r_id):
//       return true

//    // 5. If this wasn't enough, get more assumptions
//    splits: vec<assumption> = get_splits(assumptions, rule)

//    for split in splits:
//        result = case_split_internal(depth + 1, rule, assumptions.append([split]), ruleset, imps)
//        if !result:
//           return false

//     return true
// }
//
use std::collections::{HashSet, VecDeque};


// ======== Split Records ========
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OrderSplit {
    lhs: String,
    rhs: String,
}

impl From<OrderSplit> for Vec<Assumption<Pred>> {
    fn from(os: OrderSplit) -> Self {
        vec![
            Assumption::new(format!("(< {} {})", os.lhs, os.rhs)).unwrap(),
            Assumption::new(format!("(== {} {})", os.lhs, os.rhs)).unwrap(),
            Assumption::new(format!("(> {} {})", os.lhs, os.rhs)).unwrap(),
        ]
    }
}

#[derive(Clone, Debug)]
enum SplitCandidate {
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
    fn get_next_split(&mut self, rule: &Rule<Pred>) -> Option<SplitCandidate> {
        // TODO: does vars contain concrete variables or metavariables?
        let mut vars = rule.lhs.vars();
        vars.extend(rule.rhs.vars());

        let mut vars = vars.iter().map(|v| {
            assert!(v.to_string().starts_with('?'), "Variable {} does not start with ?", v);
            v.to_string().trim_start_matches('?').to_string()
        }).collect::<Vec<_>>();
        vars.sort();
        vars.dedup();


        for (i, v1) in vars.iter().enumerate() {
            for v2 in vars.iter().skip(i + 1) {
                if v1 == v2 {
                    continue;
                }

                let order_split = OrderSplit { lhs: v1.to_string(), rhs: v2.to_string() };
                if !self.done_order_splits.contains(&order_split) {
                    self.done_order_splits.insert(order_split.clone());
                    return Some(SplitCandidate::Order(order_split));
                }
            }

        }
        None
    }
}

pub fn case_split_minimize(ruleset: Ruleset<Pred>, chosen: Ruleset<Pred>, implications: ImplicationSet<Pred>) -> Ruleset<Pred> {
    let mut new_ruleset = chosen.clone();
    let mut ruleset = ruleset.clone();
    while !ruleset.is_empty() {
        let chosen = ruleset.select(1, &mut Default::default());
        if chosen.len() == 0 {
            break;
        }
        let (_, rule) = chosen.clone().into_iter().next().unwrap().clone();
        let result = !case_split(rule.clone(), new_ruleset.clone(), implications.clone());
        println!("result for {}: {}", rule, result);
        if result {
            new_ruleset.extend(chosen);
        }
    }

    new_ruleset
}

#[cfg(test)]
mod split_tests {
    use ruler::{enumo::Rule, halide::Pred};

    use crate::SplitCandidate;

    #[test]
    fn test_order_split_from() {
        use super::*;
        let os = OrderSplit { lhs: "a".to_string(), rhs: "b".to_string() };
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
fn case_split(rule: Rule<Pred>, ruleset: Ruleset<Pred>, implications: ImplicationSet<Pred>) -> bool {
    let tracker = CaseSplitTracker::new();
    println!("Case splitting on rule: {}", rule);
    case_split_internal(0, &rule, &[], &tracker, ruleset, implications)
}

fn is_false(assumptions: &[Assumption<Pred>]) -> bool {
    todo!()
    // 1. Chop the "assume" keyword from each predicate
    // 2. And them all together
    // 3. Ask Z3 if the result is unsat
    // 4. If so, return true

}

// Returns false if you should keep it. Returns true if you should throw it away.
fn case_split_internal(depth: usize, rule: &Rule<Pred>, assumptions: &[Assumption<Pred>], tracker: &CaseSplitTracker, ruleset: Ruleset<Pred>, implications: ImplicationSet<Pred>) -> bool {
    if depth > 10 {
        println!("Bailed out of case splitting at depth {}", depth);
        return false;
    }

    println!("assumptions at depth {}", depth);
    for a in assumptions {
        println!("  {}", a);
    }

    // if is_false(&assumptions) {
    //     // We can vacuously prove anything in the world where false is true
    //     return true;
    // }

    // actually, if we wanted, we could even cache this between calls.
    let mut egraph: EGraph<Pred, SynthAnalysis> = EGraph::default();
    let l_id = egraph.add_expr(&Pred::instantiate(&rule.lhs));
    let r_id = egraph.add_expr(&Pred::instantiate(&rule.rhs));

    // 1. add each assumption to the egraph.
    for a in assumptions {
        a.insert_into_egraph(&mut egraph);
    }

    let rules: Vec<Rewrite<Pred, SynthAnalysis>> = ruleset.iter().map(|r| r.rewrite.clone()).collect();

    // 2. rewrite the assumption as needed
    let runner: Runner<Pred, SynthAnalysis> = Runner::default()
        .with_egraph(egraph)
        .run(&rules);

    egraph = runner.egraph;


    // 3. run the implications that follow from the assumptions
    let runner: Runner<Pred, SynthAnalysis> = Runner::default()
        .with_egraph(egraph)
        .run(&implications.to_egg_rewrites());

    egraph = runner.egraph;

    // 4. rewrite the entire term space
    let runner: Runner<Pred, SynthAnalysis> = Runner::default()
        .with_egraph(egraph)
        .run(&rules);

    egraph = runner.egraph;

    if egraph.find(l_id) == egraph.find(r_id) {
        println!("Proved by case splitting at depth {}", depth);
        return true;
    }

    // 5. If this wasn't enough, get more assumptions
    let mut tracker = tracker.clone();
    if let Some(split) = tracker.get_next_split(rule) {
        match split {
            SplitCandidate::Order(o) => {
                let split_assumptions: Vec<Assumption<Pred>> = o.into();
                for a in &split_assumptions {
                    let new_assumptions = [assumptions, &[a.clone()]].concat();
                    let result = case_split_internal(depth + 1, rule, &new_assumptions, &tracker, ruleset.clone(), implications.clone());
                    if !result {
                        return false;
                    }

                }
            }
        }
    } else {
        println!("No more splits available at depth {}", depth);
        return false;
    }

    true
}
 

#[cfg(test)]
pub mod analysis_tests {
    use egg::Runner;
    use ruler::{enumo::{egg_to_serialized_egraph, Filter, Metric, Rule, Ruleset, Workload}, halide::Pred, recipe_utils::{base_lang, iter_metric, recursive_rules, run_workload, Lang}, DeriveType, EGraph, Limits, SynthAnalysis, SynthLanguage};

    #[tokio::test]
    pub async fn see_craziness() {
        // 1. Just give me lemmas about min and + and <.
        let mut baseline: Ruleset<Pred> = recursive_rules(Metric::Atoms, 9, Lang::new(
            &[],
            &["a", "b", "c"],
            &[&[], &["+", "min"]]
        ), Default::default(), false).await;

        let lt_rules: Ruleset<Pred> = recursive_rules(Metric::Atoms, 3, Lang::new(
            &[],
            &["a", "b", "c"],
            &[&[], &["<"]]
        ), Default::default(), false).await;

        baseline.extend(lt_rules);
        baseline.add(Rule::from_string("(min ?a ?b) ==> ?a if (< ?a ?b)").unwrap().0);

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

        // for t in lt_workload.clone().force() {
        //     println!("Workload term: {}", t);
        // }


        let new_rules = run_workload(
            lt_workload,
            None,
            baseline.clone(),
            Default::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
            false,
        ).await;


        let r: Rule<Pred> = Rule::from_string("(< (+ ?a ?b) (+ ?a ?c)) ==> (< ?b ?c)").unwrap().0;
        assert!(r.is_valid());

        let full_len = new_rules.len();
        println!("Generated {} new rules", full_len);
        new_rules.pretty_print();

        assert!(new_rules.can_derive(DeriveType::LhsAndRhs, &r, Limits::deriving()));

        let minimized = super::case_split_minimize(new_rules, Default::default(), Default::default());

        println!("Minimized to {} rules (difference of {})", minimized.len(), full_len - minimized.len());
        minimized.pretty_print();


        let mut egraph: EGraph<Pred, SynthAnalysis> = EGraph::default().with_explanations_enabled();
        let l_expr = Pred::instantiate(&r.lhs);
        let r_expr = Pred::instantiate(&r.rhs);
        let l_id = egraph.add_expr(&l_expr);
        let r_id = egraph.add_expr(&r_expr);

        let total_rules = minimized.iter().take(30).filter_map(|r| {
            if r.cond.is_some() {
                println!("Skipping conditional rule: {}", r);
                return None;
            }
            println!("Using rule: {}", r);
            Some(r.rewrite.clone())
        }
        ).collect::<Vec<_>>();

        let mut runner: Runner<Pred, SynthAnalysis> = Runner::default()
            .with_egraph(egraph)
            .run(&total_rules);

        let egraph = runner.egraph.clone();

        let serialized = egg_to_serialized_egraph(&egraph);
        serialized.to_json_file("my_favorite_egraph.json").unwrap();
        assert!(egraph.find(l_id) == egraph.find(r_id), "Failed to derive {} in egraph: ", r);
        println!("Proof:");
        let proof = runner.egraph.explain_equivalence(&l_expr, &r_expr).get_flat_string();
        println!("{}", proof);




        assert!(
            minimized.can_derive(DeriveType::LhsAndRhs, &r, Limits::deriving())
        );

    }

    #[test]
    fn thing_is_valid() {
        let r: Rule<Pred> = Rule::from_string("(< (+ ?a ?b) (+ ?a ?c)) ==> (< ?b ?c)").unwrap().0;
        assert!(r.is_valid());
    }

}
