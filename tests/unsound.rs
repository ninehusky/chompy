use ruler::{
    conditions::{
        self,
        assumption::Assumption,
        implication::Implication,
        implication_set::{run_implication_workload, ImplicationSet},
    },
    enumo::{Rule, Ruleset},
    halide::Pred,
    time_fn_call, DeriveType, Limits,
};

/// This test, as far as we can tell, used to document a situation where
/// a ruleset of rules which are all locally sound could somehow derive
/// an unsound rule.
#[test]
fn avoid_unsound_merge() {
    let wkld = conditions::generate::get_condition_workload();
    let mut base_implications: ImplicationSet<Pred> = ImplicationSet::default();
    // // and the "and" rules here.
    let and_implies_left: Implication<Pred> = Implication::new(
        "and_implies_left".into(),
        Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
        Assumption::new_unsafe("?a".to_string()).unwrap(),
    )
    .unwrap();

    base_implications.add(and_implies_left);

    let other_implications = time_fn_call!(
        "find_base_implications",
        run_implication_workload(
            &wkld,
            &["a".to_string(), "b".to_string(), "c".to_string()],
            &base_implications,
            &Default::default()
        )
    );

    base_implications.add_all(other_implications);

    println!("# base implications: {}", base_implications.len());
    let rules = r#"(< 0 ?a) <=> (> ?a 0)
(min ?a ?a) <=> ?a
(max ?a ?a) <=> (min ?a ?a)
(min ?b ?a) <=> (min ?a ?b)
(max ?b ?a) <=> (max ?a ?b)
(min ?b ?a) ==> ?a if (<= ?a ?b)
(max ?b ?a) ==> ?b if (<= ?a ?b)
(min ?b (max ?b ?a)) ==> ?b
(max ?a (min ?b ?a)) ==> ?a
(min ?a 1) ==> 1 if (< 0 ?a)
(max ?a 1) ==> ?a if  (< 0 ?a)
(min ?a 1) ==> ?a if  (<= ?a 0)
(min 0 (min ?a 1)) <=> (min ?a 0)
(max ?a (* ?a ?a)) <=> (* ?a ?a)
(min ?b (* ?a ?a)) ==> ?b if (<= ?b 0)
(max ?b (* ?a ?a)) ==> (* ?a ?a) if (<= ?b 0)
(min ?b (* ?a ?a)) ==> ?b if (< ?b 0)
(max ?b (* ?a ?a)) ==> (* ?a ?a) if (< ?b 0)
(* (min ?b ?a) (max ?b ?a)) <=> (* ?b ?a)
(min ?c (* ?b (min ?b ?a))) ==> (min ?c (* ?a (max ?b ?a))) if  (< ?c 0)
(max ?b (* ?b (max ?b ?a))) ==> (max ?a (* ?b (max ?b ?a))) if  (< ?a 0)"#;

    let mut ruleset: Ruleset<Pred> = Default::default();
    for rule in rules.split("\n") {
        if !rule.trim().is_empty() {
            if let Ok((f, b)) = Rule::from_string(rule) {
                // 1. Observe that every rule that we have is sound.
                assert!(f.is_valid());
                ruleset.add(f);
                if let Some(b) = b {
                    assert!(b.is_valid());
                    ruleset.add(b);
                }
            } else {
                panic!("Failed to parse rule: {}", rule);
            }
        }
    }

    println!("# rules: {}", ruleset.len());

    // 2. Note that this rule is unsound.
    //    It should never be the case that sound rules can derive a rule that is not valid.
    let against: Rule<Pred> = Rule::from_string("(/ (max ?x ?y) ?z) ==> 0").unwrap().0;
    assert!(!against.is_valid());

    assert!(!ruleset.can_derive(DeriveType::LhsAndRhs, &against, Limits::deriving()));
}
