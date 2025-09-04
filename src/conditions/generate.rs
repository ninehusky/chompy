use egg::{AstSize, Extractor};

use crate::conditions::implication_set::ImplicationSet;
use crate::recipe_utils::LLMUsage;
use crate::{
    enumo::{Filter, Metric, Rule, Ruleset, Scheduler, Workload},
    halide::Pred,
    recipe_utils::{recursive_rules, run_workload, Lang},
    Limits,
};

pub async fn get_condition_workload() -> Workload {
    let llm_usage = LLMUsage::None;
    // we're going to do conjunctions of ==, != with
    // variables and 0.
    let start = std::time::Instant::now();
    println!("Beginning condition workload generation");

    let the_atoms = Workload::new(&["a", "b", "c"]).append(Workload::new(&["0"]));

    let the_ints = the_atoms.clone();

    let leaves = Workload::new(&["0", "1", "(OP2 V V)"])
        .plug("V", &the_ints)
        .plug("OP2", &Workload::new(&["<", "==", "<=", "!="]));

    let branches = Workload::new(&["(OP2 V V)"])
        .plug("V", &leaves)
        .plug("OP2", &Workload::new(&["&&"]))
        .filter(Filter::Canon(vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
        ]));

    let mut eq_rules = Ruleset::default();
    eq_rules.add(
        Rule::from_string("(&& (<= ?a ?b) (<= ?b ?a)) ==> (== ?a ?b)")
            .unwrap()
            .0,
    );

    let new_rules = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(
            &["0", "1"],
            &["a", "b", "c"],
            &[&[], &["<", "<=", "==", "!=", "&&"]],
        ),
        Ruleset::default(),
        llm_usage.clone()
    ).await;

    eq_rules.extend(new_rules);

    let rules = run_workload(
        branches.clone(),
        None,
        eq_rules,
        ImplicationSet::default(),
        llm_usage.clone()
    ).await;

    let branches_better = compress(&branches, rules.clone());

    println!("Condition workload generation took: {:?}", start.elapsed());

    branches_better.filter(Filter::MetricLt(Metric::Atoms, 6))
}

pub fn compress(workload: &Workload, prior: Ruleset<Pred>) -> Workload {
    let start = std::time::Instant::now();
    println!("[compress] Starting compression of implication workload.");
    let egraph = workload.to_egraph();
    let compressed = Scheduler::Compress(Limits::minimize()).run(&egraph, &prior);

    let mut result = Workload::empty();

    let extractor = Extractor::new(&compressed, AstSize);
    for c in compressed.classes() {
        let (_, best) = extractor.find_best(c.id);

        result = result.append(Workload::new(&[best.to_string()]));
    }

    println!(
        "[compress] Compression took: {:?}, reduced {} classes to {}",
        start.elapsed(),
        egraph.number_of_classes(),
        compressed.number_of_classes()
    );

    result
}
