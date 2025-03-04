#[cfg(test)]
#[path = "./recipes/halide.rs"]
mod halide;

#[allow(unused_imports)]
mod test {
    use crate::halide::{
        halide_rules, halide_rules_for_caviar_conditional, halide_rules_for_caviar_total_only,
    };
    use ruler::halide::{egg_to_z3, Pred};
    use std::{
        str::FromStr,
        sync::Arc,
        time::{Duration, Instant},
    };

    use egg::{
        rewrite, AstSize, ConditionEqual, ConditionalApplier, Extractor, Pattern, RecExpr, Rewrite,
    };
    use ruler::{
        enumo::{Filter, Metric, Rule, Ruleset, Workload},
        logger,
        recipe_utils::{recursive_rules, run_workload, Lang},
        Limits,
    };
    use ruler::{SynthAnalysis, SynthLanguage};
    use z3::ast::Ast;

    #[test]
    fn test_conditional_deriability_direct() {
        // tests that {`if x >= 0 then x ~> |x|`} derives `if x > 5 then x ~> |x|`.
        let (rule_a, _): (Rule<Pred>, _) = Rule::from_string("x ==> (abs x) if (>= x 0)").unwrap();
        let (rule_b, _): (Rule<Pred>, _) = Rule::from_string("x ==> (abs x) if (> x 5)").unwrap();
        let mut ruleset_a = Ruleset::default();
        let mut ruleset_b = Ruleset::default();

        ruleset_a.add(rule_a.clone());
        ruleset_b.add(rule_b.clone());

        let mut cond_prop_ruleset: Ruleset<Pred> = Ruleset::default();

        cond_prop_ruleset.add(Rule::from_string("TRUE ==> (>= x 0) if (> x 5)").unwrap().0);

        let (can, cannot) = ruleset_a.derive(
            ruler::DeriveType::LhsAndRhs,
            &ruleset_b,
            Limits::deriving(),
            &Some(cond_prop_ruleset.clone()),
        );

        assert!(can.len() == 1);
        assert!(cannot.is_empty());

        let (can, cannot) = ruleset_b.derive(
            ruler::DeriveType::LhsAndRhs,
            &ruleset_a,
            Limits::deriving(),
            &Some(cond_prop_ruleset),
        );

        assert!(can.is_empty());
        assert!(cannot.len() == 1);
    }

    #[test]
    fn test_conditional_derivability_step() {
        // tests that {`if x >= 0 then x ~> |x|`} derives `if x > 5 then x ~> |x|`.
        let (rule_a, _): (Rule<Pred>, _) = Rule::from_string("x ==> (abs x) if (>= x 0)").unwrap();
        let (rule_b, _): (Rule<Pred>, _) = Rule::from_string("x ==> (abs x) if (> x 5)").unwrap();
        let mut ruleset_a = Ruleset::default();
        let mut ruleset_b = Ruleset::default();

        ruleset_a.add(rule_a.clone());
        ruleset_b.add(rule_b.clone());

        let mut cond_prop_ruleset: Ruleset<Pred> = Ruleset::default();

        cond_prop_ruleset.add(Rule::from_string("TRUE ==> (> x 4) if (> x 5)").unwrap().0);
        cond_prop_ruleset.add(Rule::from_string("TRUE ==> (>= x 0) if (> x 4)").unwrap().0);

        let (can, cannot) = ruleset_a.derive(
            ruler::DeriveType::LhsAndRhs,
            &ruleset_b,
            Limits::deriving(),
            &Some(cond_prop_ruleset.clone()),
        );

        assert!(can.len() == 1);
        assert!(cannot.is_empty());

        let (can, cannot) = ruleset_b.derive(
            ruler::DeriveType::LhsAndRhs,
            &ruleset_a,
            Limits::deriving(),
            &Some(cond_prop_ruleset),
        );

        assert!(can.is_empty());
        assert!(cannot.len() == 1);
    }

    #[test]
    fn run() {
        // Skip this test in github actions
        if std::env::var("CI").is_ok() && std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        let start = Instant::now();
        let all_rules = halide_rules_for_caviar_conditional();
        println!("done");
        return;
        let duration = start.elapsed();

        // oopsla-halide-baseline branch
        // Run on nightly 4/12/2023
        // time cargo run --release --bin halide -- synth --iters 1 --use-smt
        // real	0m2.707s
        // user	0m2.681s
        // sys	0m0.028s
        let baseline: Ruleset<Pred> = Ruleset::from_file("baseline/halide.rules");
        let oopsla_halide: Ruleset<Pred> = Ruleset::from_file("baseline/oopsla-halide.rules");
        let oopsla_duration = Duration::from_secs_f32(3.354);

        logger::write_baseline(&all_rules, "halide", &baseline, "halide", duration);

        logger::write_baseline(
            &oopsla_halide,
            "oopsla halide (1 iter)",
            &baseline,
            "halide",
            oopsla_duration,
        );
    }
}
