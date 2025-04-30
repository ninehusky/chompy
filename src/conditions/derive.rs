// This file is about minimizing implications :)

use std::str::FromStr;

use egg::Rewrite;

use crate::{enumo, halide::Pred, SynthAnalysis, SynthLanguage, ValidationResult};

use super::{validate_implication, Implication};

// We assume a low score is better.
// For now, this is just the AST size of lhs + rhs.
// later, we can use 1 / |satisfying_lhs_envs| + |satisfying_rhs_envs| as a proxy
// for weakness.
fn score<L: SynthLanguage>(imp: &Implication<L>) -> usize {
    fn size(sexp: &enumo::Sexp) -> usize {
        match sexp {
            enumo::Sexp::Atom(_) => 1,
            enumo::Sexp::List(l) => l.iter().map(size).sum(),
        }
    }

    let lhs = enumo::Sexp::from_str(&imp.lhs.to_string()).unwrap();
    let rhs = enumo::Sexp::from_str(&imp.rhs.to_string()).unwrap();

    size(&lhs) + size(&rhs)
}

// Until there are no more imps to consider:
// 1. Pop the "best" implication from imps.
// 2. Using imps :: prior, add the lhs, rhs of each implication to an **egglog** egraph.
//    In particular, add `(edge lhs rhs)` to the egraph.
// 3. Run the path-finding algorithm on the egraph.
// 4. For each remaining implication, query the egraph to see if `(path lhs rhs)` is present. If it is, throw the rule away.
// TODO: get rid of `Pred`, and boot the need to validate over to the `SynthLanguage` trait.
pub fn minimize_implications(imps: &Vec<Implication<Pred>>, prior: &Vec<Implication<Pred>>) -> (Vec<Implication<Pred>>, Vec<Implication<Pred>>) {
    let mut invalid: Vec<Implication<Pred>> = vec![];
    let mut chosen = prior.clone();
    let step_size = 1;
    let mut mut_imps = imps.clone();
    while !mut_imps.is_empty() {
        let selected = select_implications(&mut mut_imps, step_size, &mut invalid);
        chosen.extend(selected.clone());
        mut_imps = shrink_implications(&mut_imps, &chosen);
    }

    let mut new_imps = vec![];
    // return only the new implications.
    for imp in chosen {
        if !prior.contains(&imp) {
            new_imps.push(imp);
        }
    }

    (new_imps, invalid)

}


pub fn shrink_implications(imps: &Vec<Implication<Pred>>, chosen: &Vec<Implication<Pred>>) -> Vec<Implication<Pred>> {
    // 1. make new egraph
    let mut egraph = new_impl_egraph();

    // 2. add the lhs, rhs of each implication to the egraph
        // now, attempt to derive the selected implications.
        // step 2
        for imp in chosen {
            let lhs = imp.lhs.to_string();
            let rhs = imp.rhs.to_string();

            egraph.parse_and_run_program(None,
                format!("(edge \"{}\" \"{}\")", lhs, rhs).as_str()).unwrap();
        }

        // step 3
        egraph.parse_and_run_program(None, "(run-schedule (saturate find-path))").unwrap();

        let mut keep = vec![];

        // step 4
        for imp in imps {
            let lhs = imp.lhs.to_string();
            let rhs = imp.rhs.to_string();

            if !egraph.parse_and_run_program(None,
                format!("(check (path \"{}\" \"{}\"))", lhs, rhs).as_str()).is_ok() {
                // the path does not exist
                keep.push(imp.clone());
            }

        }

    keep
}

pub fn select_implications(imps: &mut Vec<Implication<Pred>>, step_size: usize, invalid: &mut Vec<Implication<Pred>>) -> Vec<Implication<Pred>> {
    let mut chosen = vec![];
    imps.sort_by(|a, b| score(b).cmp(&score(a)));

    let mut selected = vec![];

    while selected.len() < step_size {
        let popped = imps.pop();
        if let Some(imp) = popped {
            if matches!(validate_implication(imp.clone()), ValidationResult::Valid) {
                selected.push(imp.clone());
            } else {
                invalid.push(imp.clone());
            }
        } else {
            // we've run out of implications
            break;
        }
    }

    chosen.extend(selected);
    chosen

}

/// Returns an egraph initialized with the path-finding ruleset.
fn new_impl_egraph() -> egglog::EGraph {
    let mut egraph = egglog::EGraph::default();
    egraph.parse_and_run_program(None,
        r#"
        (relation edge (String String))
        (relation path (String String))

        (ruleset find-path)

        ;;; The base case.
        (rule
            ((edge ?l ?r))
            ((path ?l ?r))
            :ruleset find-path)

        ;;; The inductive case.
        (rule
            ((path ?l ?x)
             (edge ?x ?r))
            ((path ?l ?r))
            :ruleset find-path)
        "#).unwrap();
    egraph
}

#[test]
fn shrink_implications_halide_ok() {
    // let's say we have 4 candidate implications:
    // 1. (&& (> a 5) (>= a 4)) ==> (< a 1)
    // 2. (> a 5) ==> (>= a 4)
    // 3. (> a 4) ==> (>= a 0)
    // 4. (> a 5) ==> (>= a 0)

    // (1) should be thrown away because it's invalid.
    // (2) and (3) should be kept because they are valid.
    // (4) should be thrown away because it is redundant.

    // the weird "- 0 s" inside each of these is a way for us
    // to get around the fact that otherwise, all of those
    // rules would have the same score.
    // basically, we want chompy to pick (a > 5) ==> (a >= 4) and
    // (a > 4) ==> (a >= 0) as the two implications to keep,
    // and then throw away (a > 5) ==> (a >= 0).
    // this means adding a "0" to the end of each rule.
    let imps: Vec<Implication<Pred>> = vec![
        Implication {
            name: "(&& (> ?a 5) (>= ?a 4)) ==> (< ?a 1)".into(),
            lhs: "(&& (> ?a 5) (>= ?a 4))".parse().unwrap(),
            rhs: "(< ?a 1)".parse().unwrap(),
        },
        Implication {
            name: "(> ?a (- 5 0)) ==> (> ?a 4)".into(),
            lhs: "(> ?a (- 5 0))".parse().unwrap(),
            rhs: "(> ?a 4)".parse().unwrap(),
        },
        Implication {
            name: "(> ?a 4) ==> (>= ?a (- 0 0)".into(),
            lhs: "(> ?a 4)".parse().unwrap(),
            rhs: "(>= ?a (- 0 0))".parse().unwrap(),
        },
        Implication {
            name: "(> ?a (- 5 0)) ==> (>= ?a (- 0 0))".into(),
            lhs: "(> ?a (- 5 0))".parse().unwrap(),
            rhs: "(>= ?a (- 0 0))".parse().unwrap(),
        },
    ];

    let mut imps = imps.clone();
    let (new_imps, invalid) = minimize_implications(&mut imps, &mut vec![]);
    assert_eq!(invalid.len(), 1);
    assert_eq!(new_imps.len(), 2);

    let the_good_implications = vec![
        Implication {
            name: "(> ?a (- 5 0)) ==> (> ?a 4)".into(),
            lhs: "(> ?a (- 5 0))".parse().unwrap(),
            rhs: "(> ?a 4)".parse().unwrap(),
        },
        Implication {
            name: "(> ?a 4) ==> (>= ?a (- 0 0)".into(),
            lhs: "(> ?a 4)".parse().unwrap(),
            rhs: "(>= ?a (- 0 0))".parse().unwrap(),
        },
    ];

    for good_imp in the_good_implications {
        assert!(new_imps.contains(&good_imp));
    }
}

#[test]
fn score_good() {
    let imp1: Implication<Pred> = Implication {
        name: "a ==> b".into(),
        lhs: "a".parse().unwrap(),
        rhs: "b".parse().unwrap(),
    };

    let imp2: Implication<Pred> = Implication {
        name: "(&& a c) ==> b".into(),
        lhs: "(&& a c)".parse().unwrap(),
        rhs: "b".parse().unwrap(),
    };

    let implications = vec![imp1, imp2];
    let mut sorted = implications.clone();
    sorted.sort_by(|a, b| score(b).cmp(&score(a)));

    let first = sorted.pop().unwrap();
    let second = sorted.pop().unwrap();

    assert_eq!(score(&first), 2);
    assert_eq!(score(&second), 4);
    assert_eq!(first.name, "a ==> b".into());
    assert_eq!(second.name, "(&& a c) ==> b".into());
}

#[test]
fn new_impl_egraph_compiles() {
    new_impl_egraph();
}

#[test]
fn egraph_edge_relation_ok() {
    let mut egraph = new_impl_egraph();
    egraph.parse_and_run_program(None, "(edge \"a\" \"b\")").unwrap();
    egraph.parse_and_run_program(None, "(check (edge \"a\" \"b\"))").unwrap();
}

#[test]
fn egraph_path_ok() {
    let mut egraph = new_impl_egraph();
    egraph.parse_and_run_program(None, "(edge \"a\" \"b\")").unwrap();
    egraph.parse_and_run_program(None, "(edge \"b\" \"c\")").unwrap();
    egraph.parse_and_run_program(None, "(run-schedule (saturate find-path))").unwrap();
    egraph.parse_and_run_program(None, "(check (path \"a\" \"c\"))").unwrap();
    egraph.parse_and_run_program(None, "(check (path \"a\" \"b\"))").unwrap();
}
