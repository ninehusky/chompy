
use egg::{AstSize, Extractor, Rewrite};
use z3::ast::Ast;

use crate::conditions::implication_set::ImplicationSet;
use crate::enumo::Sexp;
use crate::language::SynthLanguage;
use crate::{
    enumo::{Filter, Metric, Rule, Ruleset, Scheduler, Workload},
    halide::{egg_to_z3, Pred},
    recipe_utils::{recursive_rules, run_workload, Lang}, HashSet, Limits, SynthAnalysis,
    ValidationResult,
};



// oh my god
#[derive(PartialEq, Eq)]
enum Type {
    BoolTy,
    IntTy,
}

fn well_typed(exp: &Sexp, expected_type: Type) -> bool {
    match exp {
        Sexp::Atom(_) => expected_type == Type::IntTy,
        Sexp::List(l) => {
            if let Sexp::Atom(op) = &l[0] {
                match op.as_str() {
                    "&&" | "||" => {
                        if expected_type == Type::BoolTy && l.len() == 3 {
                            l[1..].iter().all(|x| well_typed(x, Type::BoolTy))
                        } else {
                            false
                        }
                    }
                    "<" | "<=" | ">" | ">=" | "==" | "!=" => {
                        if expected_type == Type::BoolTy && l.len() == 3 {
                            l[1..].iter().all(|x| well_typed(x, Type::IntTy))
                        } else {
                            false
                        }
                    }
                    "+" | "-" | "*" | "/" | "min" | "max" => {
                        if expected_type == Type::IntTy && l.len() >= 2 {
                            l[1..].iter().all(|x| well_typed(x, Type::IntTy))
                        } else {
                            false
                        }
                    }
                    _ => panic!("Unknown operator: {}", op),
                }
            } else {
                panic!("Not well formed");
            }
        }
    }
}

fn add_term(egraph: &mut egglog::EGraph, term: &crate::enumo::Sexp) {
    egraph
        .parse_and_run_program(
            None,
            format!(
                r#"
        {term}
        (edge {term} {term}) "#
            )
            .as_str(),
        )
        .unwrap();
}

fn validate_implication(imp: Rule<Pred>, filter_equalities: bool) -> ValidationResult {
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

pub fn select(
    implications: &mut Ruleset<Pred>,
    step_size: usize,
    invalid: &mut Ruleset<Pred>,
) -> Ruleset<Pred> {
    let mut chosen = Ruleset::default();
    implications
        .0
        .sort_by(|_, rule1, _, rule2| rule1.score().cmp(&rule2.score()));

    // 2. insert step_size best candidates into self.new_rws
    let mut selected: Ruleset<Pred> = Default::default();
    while selected.len() < step_size {
        let popped = implications.0.pop();
        if let Some((_, rule)) = popped {
            if matches!(
                validate_implication(rule.clone(), true),
                ValidationResult::Valid
            ) {
                selected.add(rule.clone());
            } else {
                invalid.add(rule.clone());
            }
        } else {
            break;
        }
    }
    chosen.extend(selected);

    // 3. return chosen candidates
    chosen
}

pub fn get_condition_workload() -> Workload {
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
    );

    eq_rules.extend(new_rules);

    let rules = run_workload(
        branches.clone(),
        None,
        eq_rules,
        ImplicationSet::default(),
        Limits::synthesis(),
        Limits::minimize(),
        true,
    );

    let branches_better = compress(&branches, rules.clone());

    println!("Condition workload generation took: {:?}", start.elapsed());

    branches_better
}

fn prune_rules(rules: Vec<Rewrite<Pred, SynthAnalysis>>) -> Vec<Rewrite<Pred, SynthAnalysis>> {
    let mut result = vec![];
    let mut seen = HashSet::default();
    for rule in rules {
        if !seen.contains(&rule.name) {
            seen.insert(rule.name);
            result.push(rule);
        }
    }
    result
}

fn compress(workload: &Workload, prior: Ruleset<Pred>) -> Workload {
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

fn ruleset_to_rewrites(ruleset: &Ruleset<Pred>) -> Vec<Rewrite<Pred, SynthAnalysis>> {
    ruleset.into_iter().map(|r| r.1.rewrite.clone()).collect()
}
