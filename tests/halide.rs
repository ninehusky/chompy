#[cfg(test)]
#[path = "./recipes/halide.rs"]
mod halide;

#[cfg(test)]
mod div_mod_tests {
    #[allow(unused_imports)]
    use ruler::{
        enumo::{Rule, Ruleset, Workload},
        EGraph, SynthAnalysis,
    };
    use ruler::{SynthLanguage, ValidationResult};

    use ruler::halide::Pred;

    #[test]
    fn div_interpreter_ok() {
        let pairs = vec![
            ("(/ 1 2)", "0"),
            ("(/ -4 -2)", "2"),
            ("(/ 5 2)", "2"),
            ("(/ -5 -2)", "3"),
            // this is an instance where Halide division is
            // different from C division.
            ("(/ -5 2)", "-3"),
            ("(/ 1 0)", "0"),
        ];

        for (l, r) in pairs {
            let workload = Workload::new(&[l, r, "dummy_var"]);
            let egraph: EGraph<Pred, SynthAnalysis> = workload.to_egraph();
            let l_id = egraph.lookup_expr(&l.parse().unwrap()).unwrap();
            let r_id = egraph.lookup_expr(&r.parse().unwrap()).unwrap();
            assert_eq!(
                egraph[l_id].data.cvec, egraph[r_id].data.cvec,
                "Failed for {l} == {r}"
            );
        }
    }

    #[test]
    fn div_validation_ok() {
        let mut ruleset: Ruleset<Pred> = Default::default();
        ruleset.add(Rule::from_string("(/ 1 2) ==> 0").unwrap().0);
        ruleset.add(Rule::from_string("(/ -4 -2) ==> 2").unwrap().0);
        ruleset.add(Rule::from_string("(/ 5 2) ==> 2").unwrap().0);
        ruleset.add(Rule::from_string("(/ -5 -2) ==> 3").unwrap().0);

        for (_, rule) in ruleset {
            assert!(rule.is_valid(), "Rule is not valid: {}", rule);
        }
    }

    #[test]
    fn mod_interpreter_ok() {
        let pairs = vec![
            ("(% 1 2)", "1"),
            ("(% -4 -2)", "0"),
            ("(% 5 2)", "1"),
            ("(% -5 -2)", "1"),
            ("(% -5 2)", "1"),
            ("(% 1 0)", "0"),
        ];

        for (l, r) in pairs {
            let workload = Workload::new(&[l, r, "dummy_var"]);
            let egraph: EGraph<Pred, SynthAnalysis> = workload.to_egraph();
            let l_id = egraph.lookup_expr(&l.parse().unwrap()).unwrap();
            let r_id = egraph.lookup_expr(&r.parse().unwrap()).unwrap();
            assert_eq!(
                egraph[l_id].data.cvec, egraph[r_id].data.cvec,
                "Failed for {l} == {r}"
            );
        }
    }

    #[test]
    fn mod_validation_ok() {
        let mut ruleset: Ruleset<Pred> = Default::default();
        ruleset.add(Rule::from_string("(% 1 2) ==> 1").unwrap().0);
        ruleset.add(Rule::from_string("(% -4 -2) ==> 0").unwrap().0);
        ruleset.add(Rule::from_string("(% 5 2) ==> 1").unwrap().0);
        ruleset.add(Rule::from_string("(% -5 -2) ==> 1").unwrap().0);
        ruleset.add(Rule::from_string("(% 1 0) ==> 0").unwrap().0);

        for (_, rule) in ruleset {
            assert!(rule.is_valid(), "Rule is not valid: {}", rule);
        }
    }

    #[test]
    fn mod_axioms_valid() {
        let mut ruleset: Ruleset<Pred> = Default::default();
        ruleset.add(Rule::from_string("(<= 0 (% ?a ?b)) ==> 1").unwrap().0);
        ruleset.add(Rule::from_string("(< (% ?a ?b) (abs ?b)) ==> 1").unwrap().0);

        for (_, rule) in ruleset {
            assert!(rule.is_valid(), "Rule is not valid: {}", rule);
        }
    }

    #[test]
    fn euclidean_identity_interpreter() {
        let workload = Workload::new(&["(+ (* (/ a b) b) (% a b))", "a"]);
        let egraph: EGraph<Pred, SynthAnalysis> = workload.to_egraph();
        let a_id = egraph.lookup_expr(&"a".parse().unwrap()).unwrap();
        let b_id = egraph.lookup_expr(&"b".parse().unwrap()).unwrap();
        let expr_id = egraph
            .lookup_expr(&"(+ (* (/ a b) b) (% a b))".parse().unwrap())
            .unwrap();
        assert!(!egraph[a_id].data.cvec.is_empty());

        for (idx, a_el) in egraph[a_id].data.cvec.iter().enumerate() {
            let b_el = egraph[b_id].data.cvec.get(idx).unwrap();
            if *b_el == Some(0) {
                // Skip division by zero.
                continue;
            }
            let expr_el = egraph[expr_id].data.cvec.get(idx).unwrap();
            assert_eq!(
                a_el, expr_el,
                "Mismatch at index {idx}: a_el == {a_el:?}, b_el == {b_el:?}, expr_el == {expr_el:?}"
            );
        }
    }

    #[test]
    // The euclidean identity should be valid. Our current implementation causes SMT
    // to hang on this test, so I'm just ensuring that it's _not_ invalid for now.
    fn euclidean_identity_valid() {
        // if b != 0, then (a / b) * b + (a % b) == a
        // let rule: Rule<Pred> =
        //     Rule::from_string("(+ (* (/ ?a ?b) ?b) (% ?a ?b)) ==> ?a if (!= ?b 0)")
        //         .unwrap()
        //         .0;
        // assert!(rule.is_valid());
        assert!(!matches!(
            Pred::validate_with_cond(
                &"(+ (* (/ ?a ?b) ?b) (% ?a ?b))".parse().unwrap(),
                &"a".parse().unwrap(),
                &"(!= ?b 0)".parse().unwrap()
            ),
            ValidationResult::Invalid
        ));
    }
}

#[test]
fn div_test() {
    let pairs = vec![
        (&[1, 2], 0),
        (&[-4, -2], 2),
        (&[5, 2], 2),
        (&[-5, -2], 3),
        (&[1, 0], 0),
    ];

    for (input, expected) in pairs {
        let result = halide_division(&input[0], &input[1]);
        assert_eq!(result, expected, "Failed for input: {:?}", input);
    }
}

#[test]
fn mod_test() {
    let pairs = vec![
        (&[1, 2], 1),
        (&[-4, -2], 0),
        (&[5, 2], 1),
        (&[-5, -2], 1),
        (&[-5, 2], 1),
        (&[1, 0], 0),
    ];

    for (input, expected) in pairs {
        let result = halide_modulo(&input[0], &input[1]);
        assert_eq!(result, expected, "Failed for input: {:?}", input);
    }
}

fn halide_division(x: &i64, y: &i64) -> i64 {
    let a = *x;
    let b = *y;
    let mut ia = a;
    let mut ib = b;
    let a_neg: i64 = ia >> 63;
    let b_neg: i64 = ib >> 63;
    let b_zero = if ib == 0 { -1 } else { 0 };
    ib -= b_zero;
    ia -= a_neg;
    let mut q: i64 = ia / ib;
    q += a_neg & (!b_neg - b_neg);
    q &= !b_zero;
    return q;
}

fn halide_modulo(x: &i64, y: &i64) -> i64 {
    let a = *x;
    let b = *y;
    let a_neg: i64 = a >> 63;
    let b_neg: i64 = b >> 63;
    let b_zero = if b == 0 { -1 } else { 0 };
    let ia = a - a_neg;
    let mut r = ia % (b | b_zero);
    r += a_neg & ((b ^ b_neg) + !b_neg);
    r &= !b_zero;
    return r;
}

#[allow(unused_imports)]
mod test {
    use crate::halide::halide_rules_for_caviar_total_only;
    use ruler::{
        halide::{egg_to_z3, Pred},
        ImplicationSwitch,
    };
    use std::{
        str::FromStr,
        sync::Arc,
        time::{Duration, Instant},
    };

    use egg::{
        rewrite, AstSize, ConditionEqual, ConditionalApplier, EGraph, Extractor, Pattern, RecExpr,
        Rewrite, Runner,
    };
    use ruler::{
        enumo::{Filter, Metric, Rule, Ruleset, Scheduler, Workload},
        logger,
        recipe_utils::{recursive_rules, run_workload, Lang},
        Limits,
    };
    use ruler::{SynthAnalysis, SynthLanguage};
    use z3::ast::Ast;

    #[test]
    fn test_conditional_derivability_direct() {
        // tests that {`if x >= 0 then x ~> |x|`} derives `if x > 5 then x ~> |x|`.
        let (rule_a, _): (Rule<Pred>, _) =
            Rule::from_string("?x ==> (abs ?x) if (>= ?x 0)").unwrap();
        let (rule_b, _): (Rule<Pred>, _) =
            Rule::from_string("?a ==> (abs ?a) if (> ?a 5)").unwrap();
        let mut ruleset_a = Ruleset::default();
        let mut ruleset_b = Ruleset::default();

        ruleset_a.add(rule_a.clone());
        ruleset_b.add(rule_b.clone());

        let x_gt_5_imp_x_ge_0: Rewrite<Pred, SynthAnalysis> =
            ImplicationSwitch::new(&"(> a 5)".parse().unwrap(), &"(>= a 0)".parse().unwrap())
                .rewrite();

        let cond_prop_rws = vec![x_gt_5_imp_x_ge_0];

        let (can, cannot) = ruleset_a.derive(
            ruler::DeriveType::LhsAndRhs,
            &ruleset_b,
            Limits::deriving(),
            Some(&cond_prop_rws),
        );

        assert_eq!(can.len(), 1);
        assert!(cannot.is_empty());

        let (can, cannot) = ruleset_b.derive(
            ruler::DeriveType::LhsAndRhs,
            &ruleset_a,
            Limits::deriving(),
            Some(&cond_prop_rws),
        );

        assert!(can.is_empty());
        assert!(cannot.len() == 1);
    }

    #[test]
    fn test_conditional_derivability_step() {
        let (rule_a, _): (Rule<Pred>, _) =
            Rule::from_string("?x ==> (abs ?x) if (>= ?x 0)").unwrap();
        let (rule_b, _): (Rule<Pred>, _) =
            Rule::from_string("?x ==> (abs ?x) if (> ?x 5)").unwrap();
        let mut ruleset_a = Ruleset::default();
        let mut ruleset_b = Ruleset::default();

        ruleset_a.add(rule_a.clone());
        ruleset_b.add(rule_b.clone());

        let x_gt_5_imp_x_gt_4: Rewrite<Pred, SynthAnalysis> =
            ImplicationSwitch::new(&"(> ?x 5)".parse().unwrap(), &"(> ?x 4)".parse().unwrap())
                .rewrite();

        let x_gt_4_imp_x_ge_0: Rewrite<Pred, SynthAnalysis> =
            ImplicationSwitch::new(&"(> ?x 4)".parse().unwrap(), &"(>= ?x 0)".parse().unwrap())
                .rewrite();

        let cond_prop_rws = vec![x_gt_5_imp_x_gt_4, x_gt_4_imp_x_ge_0];

        let (can, cannot) = ruleset_a.derive(
            ruler::DeriveType::LhsAndRhs,
            &ruleset_b,
            Limits::deriving(),
            Some(&cond_prop_rws),
        );

        assert!(can.len() == 1);
        assert!(cannot.is_empty());

        let (can, cannot) = ruleset_b.derive(
            ruler::DeriveType::LhsAndRhs,
            &ruleset_a,
            Limits::deriving(),
            Some(&cond_prop_rws),
        );

        assert!(can.is_empty());
        assert!(cannot.len() == 1);
    }
}
