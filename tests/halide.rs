#[cfg(test)]
#[path = "./recipes/halide.rs"]
mod halide;

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
