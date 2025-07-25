use egg::EGraph;
use ruler::{
    conditions::implication_set::ImplicationSet,
    enumo::{build_pvec_to_patterns, PredicateMap, Rule, Ruleset, Workload},
    halide::Pred,
    SynthAnalysis,
};

/// This file contains the minimal required code to get Chompy
/// to do a bad merge of two terms which shouldn't be merged.

#[test]
fn recreate_bad_rule() {
    let wkld = Workload::new(&["(min (max a b) c)", "c"]);
    let egraph: EGraph<Pred, SynthAnalysis> = wkld.to_egraph();

    let implications: ImplicationSet<Pred> = Default::default();
    let mut prior: Ruleset<Pred> = Ruleset::default();
    // min-comm
    prior.add(Rule::from_string("(min ?a ?b) ==> (min ?b ?a)").unwrap().0);
    // max-comm
    prior.add(Rule::from_string("(max ?a ?b) ==> (max ?b ?a)").unwrap().0);
    // min-reassoc
    prior.add(
        Rule::from_string("(min (min ?a ?b) ?c) ==> (min ?a (min ?b ?c))")
            .unwrap()
            .0,
    );
    // max-reassoc
    prior.add(
        Rule::from_string("(max (max ?a ?b) ?c) ==> (max ?a (max ?b ?c))")
            .unwrap()
            .0,
    );
    // min-squish
    prior.add(
        Rule::from_string("(min ?a ?b) ==> ?a if (<= ?a ?b)")
            .unwrap()
            .0,
    );
    // max-squish
    prior.add(
        Rule::from_string("(max ?a ?b) ==> ?a if (>= ?a ?b)")
            .unwrap()
            .0,
    );

    let conditions = Workload::new(&["(<= V V)"]).plug("V", &Workload::new(&["a", "b", "c"]));
    let predicate_map = build_pvec_to_patterns(conditions);

    let candidates =
        Ruleset::conditional_cvec_match(&egraph, &prior, &predicate_map, &implications);
    assert!(candidates.contains(
        &Rule::from_string("(min (max a b) c) ==> c if (<= c b)")
            .unwrap()
            .0
    ));
}
