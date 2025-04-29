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
pub fn minimize_implications(imps: &mut Vec<Implication<Pred>>, prior: &Vec<Implication<Pred>>) -> (Vec<Implication<Pred>>, Vec<Implication<Pred>>) {
    let mut invalid: Vec<Implication<Pred>> = vec![];
    let mut chosen = prior.clone();
    let step_size = 1;
    while !imps.is_empty() {
        let selected = select_implications(imps, step_size, &mut invalid);
        println!("done selecting");
        // assert_eq!(selected.len(), 1); <-- wasn't this here in ruler?
        chosen.extend(selected.clone());

        shrink_implications(imps, &mut chosen);

    }

    let mut new_imps = vec![];
    // Return only the new rules
    for imp in imps {
        if !chosen.contains(imp) {
            new_imps.push(imp.clone());
        }
    }

    (new_imps, invalid)

}


pub fn shrink_implications(imps: &mut Vec<Implication<Pred>>, chosen: &Vec<Implication<Pred>>) -> Vec<Implication<Pred>> {
    // 1. make new egraph
    let mut egraph = new_impl_egraph();

    // 2. add the lhs, rhs of each implication to the egraph
        // now, attempt to derive the selected implications.
        // step 2
        for imp in chosen {
            let lhs = imp.lhs.to_string();
            let rhs = imp.rhs.to_string();

            egraph.parse_and_run_program(None,
                format!("(edge {} {})", lhs, rhs).as_str()).unwrap();
        }

        // step 3
        egraph.parse_and_run_program(None, "(run-schedule (saturate find-path))").unwrap();

        let mut keep = vec![];

        // step 4
        for imp in imps {
            let lhs = imp.lhs.to_string();
            let rhs = imp.rhs.to_string();

            if !egraph.parse_and_run_program(None,
                format!("(check (path {} {}))", lhs, rhs).as_str()).is_ok() {
                // the path does not exist
                keep.push(imp.clone());
            }

        }

    keep
}

pub fn select_implications(imps: &mut Vec<Implication<Pred>>, step_size: usize, invalid: &mut Vec<Implication<Pred>>) -> Vec<Implication<Pred>> {
    let mut chosen = vec![];
    imps.sort_by(| a, b| score(a).cmp(&score(b)));

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
