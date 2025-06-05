use std::sync::Arc;
use std::str::FromStr;

use z3::ast::Ast;
use egg::{Analysis, Applier, Language, Pattern, Rewrite, Var};

use crate::{enumo, SynthAnalysis, SynthLanguage, ValidationResult};
use crate::halide::{Pred, egg_to_z3};

pub mod generate;
mod derive;

#[derive(Clone, PartialEq, Debug)]
pub struct Implication<L: SynthLanguage> {
    pub name: Arc<str>,
    lhs: Pattern<L>,
    rhs: Pattern<L>,
}

pub fn validate_implication(imp: Implication<Pred>, filter_equalities: bool) -> ValidationResult {
    let mut cfg = z3::Config::new();
    cfg.set_timeout_msec(1000);
    let ctx = z3::Context::new(&cfg);
    let solver = z3::Solver::new(&ctx);
    let lexpr = egg_to_z3(&ctx, Pred::instantiate(&imp.lhs).as_ref());
    let rexpr = egg_to_z3(&ctx, Pred::instantiate(&imp.rhs).as_ref());
    // assert that lexpr --> rexpr.

    // 1. we want to get rid of trivial implications
    // because p -> q == !p or q, we can just check if
    // - the LHS is not equal to 0, and
    // - the RHS is not equal to 1.
    
    let zero = z3::ast::Int::from_i64(&ctx, 0);
    let one = z3::ast::Int::from_i64(&ctx, 1);

    // ask the solver to find a model where the LHS is true.
    solver.assert(&lexpr._eq(&zero).not());

    // if it can't, then the LHS is trivially false
    if matches!(solver.check(), z3::SatResult::Unsat) {
        // it's "invalid" in the sense that we want to ditch this implication because it's
        // trivially true.
        return ValidationResult::Invalid;
    }

    solver.reset();

    // ask the solver to find a model where the RHS is false.
    solver.assert(&one._eq(&rexpr).not());

    // if it can't, then the RHS is trivially true.
    if matches!(solver.check(), z3::SatResult::Unsat) {
        return ValidationResult::Invalid;
    }


    solver.reset();

    if filter_equalities {
        // if we are filtering equalities, we can just check if the LHS is equal to the RHS.
        // if they are equal, then the implication is trivially true.
        solver.assert(&lexpr._eq(&rexpr).not());
        if solver.check() == z3::SatResult::Unsat {
            // we've found not a one-directional implication, but a two-way equivalence.
            return ValidationResult::Invalid;
        }   
        solver.reset();
    }


    // with trivial implications out of the way, we can now check if the non-trivial implication is valid.

    // println!("checking implication: {} -> {}", lexpr, rexpr);
    solver.assert(&z3::ast::Bool::implies(&lexpr._eq(&zero).not(), &rexpr._eq(&zero).not()).not());

    let result = solver.check();


    match result {
        z3::SatResult::Unsat => ValidationResult::Valid,
        z3::SatResult::Unknown => ValidationResult::Unknown,
        z3::SatResult::Sat => ValidationResult::Invalid,
    }


}


struct EqApplier {
    a: Var,
    b: Var,
}

impl <L: Language, N: Analysis<L>> Applier<L, N> for EqApplier {
    fn apply_one(
            &self,
            egraph: &mut egg::EGraph<L, N>,
            _eclass: egg::Id,
            subst: &egg::Subst,
            _searcher_ast: Option<&egg::PatternAst<L>>,
            _rule_name: egg::Symbol,
        ) -> Vec<egg::Id> {
        let a = subst.get(self.a).unwrap();
        let b = subst.get(self.b).unwrap();
        if egraph.union(*a, *b) {
            vec![*a, *b]
        } else {
            vec![]
        }
    }
}


pub fn merge_eqs() -> Rewrite<Pred, SynthAnalysis> {
    let searcher: Pattern<Pred> = "(istrue (== ?a ?b))".parse().unwrap();
    // union ?a and ?b.
    let applier = EqApplier {
        a: "?a".parse().unwrap(),
        b: "?b".parse().unwrap(),
    };

    Rewrite::new("istrue-eqs", searcher, applier).unwrap()
}

pub mod tests {
    use egg::{EGraph, Runner};

    use crate::{enumo::egg_to_serialized_egraph, ImplicationSwitch};

    use super::*;
    #[test]
    fn merge_eqs_merges() {
        let rule: ImplicationSwitch<Pred> = ImplicationSwitch {
            parent_cond: "(!= ?x 0)".parse().unwrap(),
            my_cond: "(== (/ ?x ?x) 1)".parse().unwrap(),
        };

        let egraph = &mut EGraph::<Pred, SynthAnalysis>::default();

        egraph.add_expr(&"(istrue (!= x 0))".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[rule.rewrite(), merge_eqs()]);

    let egraph = runner.egraph.clone();

    let serialized = egg_to_serialized_egraph(&egraph);
    serialized.to_json_file("implication_toggle_equality_simple.json").unwrap();


    assert!(egraph.lookup_expr(&"(istrue (== (/ x x) 1))".parse().unwrap()).is_some());

    assert_eq!(egraph.lookup_expr(&"(/ x x)".parse().unwrap()), egraph.lookup_expr(&"1".parse().unwrap()));


    }
}