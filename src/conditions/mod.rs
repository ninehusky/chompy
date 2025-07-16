
use egg::{Pattern, Rewrite};

use crate::conditions::implication::{EqApplier, Implication};
use crate::halide::Pred;
use crate::{SynthAnalysis, ValidationResult};

pub mod assumption;
mod derive;
pub mod generate;
pub mod implication;
pub mod implication_set;
mod manager;

pub fn merge_eqs() -> Rewrite<Pred, SynthAnalysis> {
    let searcher: Pattern<Pred> = "(assume (== ?a ?b))".parse().unwrap();
    // union ?a and ?b.
    let applier = EqApplier {
        a: "?a".parse().unwrap(),
        b: "?b".parse().unwrap(),
    };

    Rewrite::new("assume-eqs", searcher, applier).unwrap()
}

pub fn validate_implication(imp: Implication<Pred>, filter_equalities: bool) -> ValidationResult {
    ValidationResult::Invalid
    // let mut cfg = z3::Config::new();
    // cfg.set_timeout_msec(1000);
    // let ctx = z3::Context::new(&cfg);
    // let solver = z3::Solver::new(&ctx);
    // let lexpr = egg_to_z3(&ctx, Pred::instantiate(&imp.lhs).as_ref());
    // let rexpr = egg_to_z3(&ctx, Pred::instantiate(&imp.rhs).as_ref());
    // // assert that lexpr --> rexpr.

    // // 1. we want to get rid of trivial implications
    // // because p -> q == !p or q, we can just check if
    // // - the LHS is not equal to 0, and
    // // - the RHS is not equal to 1.

    // let zero = z3::ast::Int::from_i64(&ctx, 0);
    // let one = z3::ast::Int::from_i64(&ctx, 1);

    // // ask the solver to find a model where the LHS is true.
    // solver.assert(&lexpr._eq(&zero).not());

    // // if it can't, then the LHS is trivially false
    // if matches!(solver.check(), z3::SatResult::Unsat) {
    //     // it's "invalid" in the sense that we want to ditch this implication because it's
    //     // trivially true.
    //     return ValidationResult::Invalid;
    // }

    // solver.reset();

    // // ask the solver to find a model where the RHS is false.
    // solver.assert(&one._eq(&rexpr).not());

    // // if it can't, then the RHS is trivially true.
    // if matches!(solver.check(), z3::SatResult::Unsat) {
    //     return ValidationResult::Invalid;
    // }

    // solver.reset();

    // if filter_equalities {
    //     // if we are filtering equalities, we can just check if the LHS is equal to the RHS.
    //     // if they are equal, then the implication is trivially true.
    //     solver.assert(&lexpr._eq(&rexpr).not());
    //     if solver.check() == z3::SatResult::Unsat {
    //         // we've found not a one-directional implication, but a two-way equivalence.
    //         return ValidationResult::Invalid;
    //     }
    //     solver.reset();
    // }

    // // with trivial implications out of the way, we can now check if the non-trivial implication is valid.

    // // println!("checking implication: {} -> {}", lexpr, rexpr);
    // solver.assert(&z3::ast::Bool::implies(&lexpr._eq(&zero).not(), &rexpr._eq(&zero).not()).not());

    // let result = solver.check();

    // match result {
    //     z3::SatResult::Unsat => ValidationResult::Valid,
    //     z3::SatResult::Unknown => ValidationResult::Unknown,
    //     z3::SatResult::Sat => ValidationResult::Invalid,
    // }
}
