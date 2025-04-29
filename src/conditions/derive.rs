// This file is about minimizing implications :)

use egg::Rewrite;

use crate::{halide::Pred, SynthAnalysis};

// Until there are no more imps to consider:
// 1. Pop the "best" implication from imps.
// 2. Using imps :: prior, add the lhs, rhs of each implication to an **egglog** egraph.
//    In particular, add `(edge lhs rhs)` to the egraph.
// 3. Run the path-finding algorithm on the egraph.
// 4. For each remaining implication, query the egraph to see if `(path lhs rhs)` is present. If it is, throw the rule away.
pub fn minimize_implications(imps: Vec<Rewrite<Pred, SynthAnalysis>>, prior: Vec<Rewrite<Pred, SynthAnalysis>>) -> Vec<Rewrite<Pred, SynthAnalysis>> {
    vec![]
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