use std::str::FromStr;

use egg::{AstSize, EClass, Extractor, Id, Pattern, RecExpr, Rewrite, Runner};
use env_logger::filter;
use z3::ast::Ast;

use crate::conditions::assumption::Assumption;
use crate::conditions::derive::{egg_to_egglog, new_impl_egraph};
use crate::conditions::implication_set::ImplicationSet;
use crate::enumo::Sexp;
use crate::language::SynthLanguage;
use crate::{
    conditions::{derive::minimize_implications, Implication},
    enumo::{Filter, Metric, Rule, Ruleset, Scheduler, Workload},
    halide::{egg_to_z3, Pred},
    recipe_utils::{base_lang, iter_metric, recursive_rules, run_workload, Lang},
    CVec, EGraph, HashMap, HashSet, ImplicationSwitch, IndexMap, Limits, Signature, SynthAnalysis,
    ValidationResult,
};

use egglog::{extract, EGraph as EgglogEGraph};

use super::derive::select_implications;

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
                println!("{} is valid", rule.name);
                selected.add(rule.clone());
            } else {
                println!("{} is invalid", rule.name);
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

/// Find candidates by CVec matching
/// (this returns a Ruleset for now, even though these are not actually rewrite rules.)
pub fn pvec_match(
    egraph: &EGraph<Pred, SynthAnalysis>,
    impl_egraph: &mut EgglogEGraph,
) -> Ruleset<Pred> {
    fn should_filter(term: String) -> bool {
        !(term.starts_with("(<")
            || term.starts_with("(<=")
            || term.starts_with("(>")
            || term.starts_with("(>=")
            || term.starts_with("(&&")
            || term.starts_with("(||")
            || term.starts_with("(==")
            || term.starts_with("(!="))
    }

    let time_start = std::time::Instant::now();

    println!(
        "starting cvec match with {} eclasses",
        egraph.number_of_classes()
    );

    let not_all_none: Vec<&EClass<Pred, Signature<Pred>>> = egraph
        .classes()
        .filter(|x| x.data.cvec.iter().any(|v| v.is_some()))
        .collect();

    println!("not all none: {}", not_all_none.len());

    let compare = |cvec1: &CVec<Pred>, cvec2: &CVec<Pred>| -> bool {
        for tup in cvec1.iter().zip(cvec2) {
            match tup {
                // if not a -> b == if not (not a or b) == if not a and b
                (Some(a), Some(b)) if (*a != 0) && (*b == 0) => return false,
                _ => (),
            }
        }
        true
    };

    let extract = Extractor::new(egraph, AstSize);
    let mut by_first: IndexMap<Option<i64>, Vec<Id>> = IndexMap::default();
    for class in &not_all_none {
        // println!("cvec: {:?}", class.data.cvec[0].clone());
        by_first
            .entry(class.data.cvec[0].clone())
            .or_insert_with(Vec::new)
            .push(class.id);
    }

    let empty = vec![];
    let first_none = by_first.get(&None).cloned().unwrap_or(empty);
    let mut candidates: Ruleset<Pred> = Ruleset::default();

    let one_id = egraph.lookup_expr(&"1".parse().unwrap()).unwrap();
    let zero_id = egraph.lookup_expr(&"0".parse().unwrap()).unwrap();

    for (value, classes) in by_first {
        let mut all_classes = classes.clone();
        if value.is_some() {
            all_classes.extend(first_none.clone());
        }

        for (i, class1) in egraph.classes().enumerate() {
            // let class1 = &egraph[all_classes[i]];
            for class2 in egraph.classes() {
                if class1.id == class2.id {
                    continue;
                }

                if class1.id == zero_id {
                    continue;
                }

                if class2.id == one_id {
                    continue;
                }

                let (_, e1) = extract.find_best(class1.id);
                let (_, e2) = extract.find_best(class2.id);

                // if class1's cvec is all zeros...
                if class1
                    .data
                    .cvec
                    .iter()
                    .all(|v| v.is_none() || *v == Some(0))
                {
                    // skip it.
                    continue;
                }

                // if class2's cvec is all ones...
                if class2
                    .data
                    .cvec
                    .iter()
                    .all(|v| v.is_none() || *v == Some(1))
                {
                    // skip it.
                    continue;
                }

                if compare(&class1.data.cvec, &class2.data.cvec) {
                    // create the implication rule.
                    let map = &mut HashMap::default();
                    let l_pat = Pred::generalize(&e1, map);
                    let r_pat = Pred::generalize(&e2, map);

                    // if the right hand side refers to variables which are not in the left hand side,
                    // then skip.
                    if r_pat.vars().iter().any(|v| !l_pat.vars().contains(v)) {
                        continue;
                    }

                    if should_filter(l_pat.to_string()) || should_filter(r_pat.to_string()) {
                        continue;
                    }

                    let egglog_lhs =
                        egg_to_egglog(&Sexp::from_str(e1.to_string().as_str()).unwrap());
                    let egglog_rhs =
                        egg_to_egglog(&Sexp::from_str(e2.to_string().as_str()).unwrap());

                    println!("querying: (check (path {} {}))", egglog_lhs, egglog_rhs);

                    let lhs_sexp = Sexp::from_str(&l_pat.to_string()).unwrap();
                    if !well_typed(&lhs_sexp, Type::BoolTy) {
                        println!("skipping ill-typed lhs: {}", lhs_sexp);
                        continue;
                    }

                    let rhs_sexp = Sexp::from_str(&r_pat.to_string()).unwrap();
                    if !well_typed(&rhs_sexp, Type::BoolTy) {
                        println!("skipping ill-typed rhs: {}", rhs_sexp);
                        continue;
                    }

                    impl_egraph
                        .parse_and_run_program(None, &format!("(check {})", egglog_lhs))
                        .unwrap();

                    impl_egraph
                        .parse_and_run_program(None, &format!("(check {})", egglog_rhs))
                        .unwrap();

                    if impl_egraph
                        .parse_and_run_program(
                            None,
                            &format!("(check (path {} {}))", egglog_lhs, egglog_rhs),
                        )
                        .is_ok()
                    {
                        println!("skipping rule: {} -> {} because it is already in the implication egraph", l_pat, r_pat);
                        continue;
                    } else {
                        let error = impl_egraph
                            .parse_and_run_program(
                                None,
                                &format!("(check (path {} {}))", egglog_lhs, egglog_rhs),
                            )
                            .err();
                        if let Some(err) = error {
                            println!("error: {}", err);
                        }
                        println!("adding rule: {} -> {}", l_pat, r_pat);
                    }

                    candidates.add(Rule {
                        name: format!("{} -> {}", e1, e2).into(),
                        lhs: l_pat.clone(),
                        rhs: r_pat.clone(),
                        rewrite: ImplicationSwitch::new(&l_pat, &r_pat).rewrite(),
                        cond: None,
                        true_count: None,
                    });
                }
            }
        }
    }

    println!(
        "cvec match finished in {} ms",
        time_start.elapsed().as_millis()
    );

    candidates
}

pub fn get_condition_workload() -> Workload {
    // we're going to do conjunctions of ==, != with
    // variables and 0.

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
        Rule::from_string("(&& (<= ?a ?b) (<= ?b ?a)) ==> (== ?a ?b)".into())
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

    println!("rules: {}", rules.len());
    for r in rules.iter() {
        println!("{}", r);
    }

    let branches_better = compress(&branches, rules.clone());

    let branches_forced = branches_better.force();

    println!("theWORKloadD");

    for t in branches_forced.iter() {
        println!("{}", t);
    }

    println!("size before: {}", branches.force().len());
    println!("size after: {}", branches_forced.len());

    branches_better
}

fn prune_rules(rules: Vec<Rewrite<Pred, SynthAnalysis>>) -> Vec<Rewrite<Pred, SynthAnalysis>> {
    let mut result = vec![];
    let mut seen = HashSet::default();
    for rule in rules {
        if !seen.contains(&rule.name) {
            seen.insert(rule.name.clone());
            result.push(rule);
        }
    }
    result
}

fn compress(workload: &Workload, prior: Ruleset<Pred>) -> Workload {
    let egraph = workload.to_egraph();
    let compressed = Scheduler::Compress(Limits::minimize()).run(&egraph, &prior);

    let mut result = Workload::empty();

    let extractor = Extractor::new(&compressed, AstSize);
    for c in compressed.classes() {
        let (_, best) = extractor.find_best(c.id);

        result = result.append(Workload::new(&[best.to_string()]));
    }

    result
}

fn ruleset_to_rewrites(ruleset: &Ruleset<Pred>) -> Vec<Rewrite<Pred, SynthAnalysis>> {
    ruleset.into_iter().map(|r| r.1.rewrite.clone()).collect()
}
