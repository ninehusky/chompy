use ruler::{conditions::implication_set::ImplicationSet, enumo::{Rule, Ruleset}, halide::Pred};

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



// Returns true if you should keep it, false otherwise.
fn case_split(rule: Rule<Pred>, ruleset: Ruleset<Pred>, implications: ImplicationSet<Pred>) -> bool {
    case_split_internal(0, &rule, ruleset, implications)
}

fn case_split_internal(depth: usize, rule: &Rule<Pred>, ruleset: Ruleset<Pred>, implications: ImplicationSet<Pred>) -> bool {
    todo!()
}
 

#[cfg(test)]
pub mod analysis_tests {
    use ruler::{enumo::{Filter, Metric, Ruleset, Workload}, halide::Pred, recipe_utils::{base_lang, iter_metric, recursive_rules, run_workload, Lang}, Limits};

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

        for r in baseline.iter() {
            println!("{r}");
        }

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

        for r in new_rules.iter() {
            println!("{r}");
        }

    }

}
