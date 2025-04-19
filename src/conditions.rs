use egg::{AstSize, EClass, Extractor, Id, RecExpr, Rewrite, Runner};
use z3::ast::Ast;

use crate::{enumo::{Filter, Metric, Rule, Ruleset, Scheduler, Workload}, halide::{egg_to_z3, Pred}, recipe_utils::{recursive_rules, run_workload, Lang}, CVec, EGraph, HashMap, HashSet, ImplicationSwitch, IndexMap, Limits, Signature, SynthAnalysis, ValidationResult};
use crate::language::SynthLanguage;

#[test]
fn test_it() {
    get_condition_propagation_rules_halide();
}

pub fn get_condition_propagation_rules_halide() -> Vec<Rewrite<Pred, SynthAnalysis>> {
    // 1. enumerate the condition workload.
    // we can discuss further about if this needs to be a separate step, or if
    // there's some clever reusing of the "term workload" that we can do.
    let wkld = get_condition_workload();

    println!("step 1 done");

    // 2. put it in an e-graph.
    let egraph: EGraph<Pred, SynthAnalysis> = wkld.to_egraph();

    println!("step 2 done");

    // 3. cvec matching.
    let mut candidates = pvec_match(&egraph);

    let mut good_candidates = Ruleset::default();

    let mut names = HashSet::default();

    for c in candidates {
        if names.contains(&c.1.rewrite.name.to_string()) {
            continue;
        } else {
            names.insert(c.1.rewrite.name.to_string());
        }
        if !c.1.rewrite.name.to_string().contains("implies 1") {
            good_candidates.add(c.1);

        }
    }

    candidates = good_candidates.clone();

    println!("candidates: {}", candidates.len());

    // for c in &candidates {
    //     println!("{}", c.0);
    // }

    println!("step 3 done");

    // 4. minimization.
    let result = minimize(&mut candidates, Ruleset::default(), Scheduler::Compress(Limits::minimize()));

    println!("step 4 done");

    for r in result.0 {
        println!("{}", r.1);
    }

    vec![]
}

fn validate_implication(imp: Rule<Pred>) -> ValidationResult {
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
        panic!("{} is trivially false", imp.lhs.to_string());
        return ValidationResult::Invalid;
    }

    solver.reset();

    // ask the solver to find a model where the RHS is false.
    solver.assert(&one._eq(&rexpr).not());

    // if it can't, then the RHS is trivially true.
    if matches!(solver.check(), z3::SatResult::Unsat) {
        panic!("{} is trivially true", imp.rhs.to_string());
        return ValidationResult::Invalid;
    }



    solver.reset();

    // with trivial implications out of the way, we can now check if the non-trivial implication is valid.

    println!("checking implication: {} -> {}", lexpr, rexpr);
    solver.assert(&z3::ast::Bool::implies(&lexpr._eq(&zero).not(), &rexpr._eq(&zero).not()).not());

    let result = solver.check();
    println!("result: {:?}", result);


    match result {
        z3::SatResult::Unsat => ValidationResult::Valid,
        z3::SatResult::Unknown => ValidationResult::Unknown,
        z3::SatResult::Sat => ValidationResult::Invalid,
    }


}

pub fn select(implications: &mut Ruleset<Pred>, step_size: usize, invalid: &mut Ruleset<Pred>) -> Ruleset<Pred> {
        let mut chosen = Ruleset::default();
        implications.0
            .sort_by(|_, rule1, _, rule2| rule1.score().cmp(&rule2.score()));

        // 2. insert step_size best candidates into self.new_rws
        let mut selected: Ruleset<Pred> = Default::default();
        while selected.len() < step_size {
            let popped = implications.0.pop();
            if let Some((_, rule)) = popped {

                if matches!(validate_implication(rule.clone()), ValidationResult::Valid) {
                    println!("{} is valid", rule);
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


    fn shrink(roots: &Vec<RecExpr<Pred>>, implications: &Ruleset<Pred>, chosen: &Ruleset<Pred>, scheduler: Scheduler) -> Ruleset<Pred> {

        println!("candidates left: {}", implications.len());
        // 1. make new egraph
        let mut egraph = EGraph::default();

        // 2. add all the roots to the e-graph.
        for root in roots {
            println!("adding (istrue {})", root);
            egraph.add_expr(&format!("(istrue {})", root).parse().unwrap());
        }

        // 3. compress with the rules we've chosen so far
        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph)
            .with_iter_limit(Limits::minimize().iter)
            .with_node_limit(Limits::minimize().node);

        let runner = runner.run(&ruleset_to_rewrites(chosen));

        let egraph = runner.egraph.clone();

        let mut keep = Ruleset::default();


        // 4. go through candidates and for a candidate (l --> r),
        // if (istrue l) and (istrue r) is in the e-graph, then it 
        // is no longer a candidate.
        for (_, rule) in implications {
            let l = Pred::instantiate(&rule.lhs);
            let r = Pred::instantiate(&rule.rhs);

            if egraph.lookup_expr(&l).is_some() &&
                egraph.lookup_expr(&r).is_some() {
                continue;
            } else {
                keep.add(rule.clone())
            }
        }

        keep
    }

/// Minimization algorithm for rule selection
///     while there are still candidates to choose:
///         1. select the best rule candidate
///         2. filter out candidates that are redundant given the addition of the selected rule
pub fn minimize(implications: &mut Ruleset<Pred>, prior: Ruleset<Pred>, scheduler: Scheduler) -> (Ruleset<Pred>, Ruleset<Pred>) {
    let mut invalid: Ruleset<Pred> = Default::default();
    let mut chosen = prior.clone();
    let step_size = 1;
    while !implications.is_empty() {
        let selected = select(implications, step_size, &mut invalid);
        println!("done selecting");
        // assert_eq!(selected.len(), 1); <-- wasn't this here in ruler?
        chosen.extend(selected.clone());

        let roots = get_roots(&chosen);

        println!("roots: {}", roots.len());

        for root in &roots {
            println!("root: {}", root);
        }

        shrink(&get_roots(&chosen), implications, &chosen, scheduler);
    }
    // Return only the new rules
    chosen.remove_all(prior);

    (chosen, invalid)
}

fn get_roots(selected: &Ruleset<Pred>) -> Vec<RecExpr<Pred>> {
    let mut lhss = selected
        .0
        .iter()
        .map(|(_, rule)| Pred::instantiate(&rule.lhs))
        .collect::<HashSet<_>>();

    let mut rhss = selected
        .0
        .iter()
        .map(|(_, rule)| Pred::instantiate(&rule.rhs))
        .collect::<HashSet<_>>();

    // the roots are all left hand sides which are not in the right hand sides.

    lhss.retain(|x| !rhss.contains(x));

    lhss.into_iter().collect()
}

/// Find candidates by CVec matching
/// Pairs of e-classes with equivalent CVecs are rule candidates.
/// (this returns a Ruleset for now, even though these are not actually rewrite rules.)
pub fn pvec_match(egraph: &EGraph<Pred, SynthAnalysis>) -> Ruleset<Pred> {
    let time_start = std::time::Instant::now();
    // cvecs [𝑎1, . . . , 𝑎𝑛] and [𝑏1, . . . , 𝑏𝑛] match iff:
    // ∀𝑖. 𝑎𝑖 = 𝑏𝑖 ∨ 𝑎𝑖 = null ∨ 𝑏𝑖 = null and ∃𝑖. 𝑎𝑖 = 𝑏𝑖 ∧ 𝑎𝑖 ≠ null ∧ 𝑏𝑖 ≠ null

    println!(
        "starting cvec match with {} eclasses",
        egraph.number_of_classes()
    );

    let not_all_none: Vec<&EClass<Pred, Signature<Pred>>> = egraph
        .classes()
        .filter(|x| x.data.cvec.iter().any(|v| v.is_some()))
        .collect();

    let compare = |cvec1: &CVec<Pred>, cvec2: &CVec<Pred>| -> bool {
        for tup in cvec1.iter().zip(cvec2) {
            match tup {
                // if not a -> b == if not (not a or b) == if not a and b
                // if not (not a or q)
                (Some(a), Some(b)) if !((*a != 0) && (*b != 0)) => return false,
                _ => (),
            }
        }
        true
    };
    let extract = Extractor::new(egraph, AstSize);
    let mut by_first: IndexMap<Option<i64>, Vec<Id>> = IndexMap::default();
    for class in &not_all_none {
        by_first
            .entry(class.data.cvec[0].clone())
            .or_insert_with(Vec::new)
            .push(class.id);
    }

    let empty = vec![];
    let first_none = by_first.get(&None).cloned().unwrap_or(empty);

    let mut candidates: Ruleset<Pred> = Ruleset::default();

    for (value, classes) in by_first {
        let mut all_classes = classes.clone();
        if value.is_some() {
            all_classes.extend(first_none.clone());
        }

        for i in 0..all_classes.len() {
            for j in i + 1..all_classes.len() {
                let class1 = &egraph[all_classes[i]];
                let class2 = &egraph[all_classes[j]];
                if compare(&class1.data.cvec, &class2.data.cvec) {
                    let (_, e1) = extract.find_best(class1.id);
                    let (_, e2) = extract.find_best(class2.id);
                    // create the implication rule.
                    let map = &mut HashMap::default();
                    let l_pat = Pred::generalize(&e1, map);
                    let r_pat = Pred::generalize(&e2, map);

                    // if the right hand side refers to variables which are not in the left hand side,
                    // then skip.

                    if r_pat.vars().iter().any(|v| !l_pat.vars().contains(v)) {
                        continue;
                    }

                    candidates.add(Rule {
                        name: format!("{} -> {}", e1, e2).into(),
                        lhs: l_pat.clone(),
                        rhs: r_pat.clone(),
                        rewrite: ImplicationSwitch::new(
                            &l_pat,
                            &r_pat,
                        ).rewrite(),
                        cond: None,
                    });


                    candidates.add_from_recexprs(&e1, &e2);
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

fn get_condition_workload() -> Workload {
    let ints = Workload::new(&["(OP1 V)", "(OP2 V V)"])
        .plug("V", &Workload::new(&["a", "b","c", "0", "1"]))
        .plug("OP1", &Workload::new(&["abs"]))
        .plug("OP2", &Workload::new(&["+", "-", "*", "/", "min", "max"]));

    let rules: Ruleset<Pred> = run_workload(
        ints.clone(),
        Ruleset::default(),
        Limits::synthesis(),
        Limits::minimize(),
        true,
        None,
        None
    );

    println!("size before: {}", ints.force().len());
    let ints_better = compress(&ints, rules.clone());

    let ints_forced = ints_better.force();
    println!("size after: {}", ints_forced.len());

    let int2bools = Workload::new(&["(OP2 V V)", "0", "1"])
        .plug("V", &ints_better)
        .plug("OP2", &Workload::new(&["<", "<=", ">", ">="]));

    let rules: Ruleset<Pred> = recursive_rules(Metric::Atoms, 5,
        Lang::new(
            &["0", "1"],
            &["a", "b", "c"],
            &[&[], &["<", "<=", ">", ">="]]
        ),
        Ruleset::default(),
    );

    println!("size before: {}", int2bools.force().len());

    let int2bools_better = compress(&int2bools, rules);

    println!("size after: {}", int2bools_better.force().len());
    int2bools_better
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
