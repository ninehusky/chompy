// This file is about minimizing implications :)

use std::str::FromStr;

use egg::Rewrite;

use crate::{enumo::{self, Sexp}, halide::Pred, SynthAnalysis, SynthLanguage, ValidationResult};

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
    let mut egraph = new_impl_egraph();
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
    fn add_term(egraph: &mut egglog::EGraph, term: &enumo::Sexp) {
        egraph.parse_and_run_program(None, format!(r#"
            {term}
            (edge {term} {term}) "#).as_str()).unwrap();
    }
    
    
    fn egg_to_egglog(term: &Sexp) -> Sexp {
        match term {
            Sexp::Atom(a) => {
                if let Ok(num) = a.parse::<i64>() {
                    return Sexp::Atom(format!("(Lit {})", num.to_string()));
                } else if a.starts_with("?") {
                    // a is a meta-variable, leave it alone.
                    return Sexp::Atom(a.into());
                } else {
                    return Sexp::Atom(format!("(Var \"{}\")", a).into());
                }

            }
            Sexp::List(l) => {
                assert!(l.len() > 1);
                let op = if let Some(Sexp::Atom(a)) = l.first() {
                    match a.as_ref() {
                        "abs" => "Abs",
                        "<" => "Lt",
                        "<=" => "Leq",
                        ">" => "Gt",
                        ">=" => "Geq",
                        "==" => "Eq",
                        "!=" => "Neq",
                        "->" => "Implies",
                        "!" => "Not",
                        "-" => {
                            if l.len() == 2 {
                                "Neg"
                            } else if l.len() == 3 {
                                "Sub"
                            } else {
                                panic!("expected unary negation")
                            }
                        }
                        "&&" => "And",
                        "||" => "Or",
                        "^" => "Xor",
                        "+" => "Add",
                        "*" => "Mul",
                        "/" => "Div",
                        "%" => "Mod",
                        "min" => "Min",
                        "max" => "Max",
                        "select" => "Select",
                        _ => panic!("unknown operator: {}", a),
                    }
                } else {
                    panic!("expected first element to be an atom")
                };


                let mut new_list = vec![Sexp::Atom(op.into())];
                for item in &l[1..] {
                    new_list.push(egg_to_egglog(item));
                }
                Sexp::List(new_list)
            }
        }


    }

        // 1. make new egraph
        let mut egraph = new_impl_egraph();

        // 2. add the prior implications as rules to the egraph.
        for imp in chosen {
            println!("implication: {}", imp.name);
            // keep these as terms with meta-variables.
            let lhs = egg_to_egglog(&enumo::Sexp::from_str(&imp.lhs.to_string()).unwrap());
            let rhs = egg_to_egglog(&enumo::Sexp::from_str(&imp.rhs.to_string()).unwrap());

            egraph.parse_and_run_program(None,
                format!(r#"
                (rule
                    ({lhs}
                     {rhs})
                    ((edge {lhs} {rhs}))
                    :ruleset find-path)
                "#).as_str()).unwrap();

        }

        // let's just add this implication to the egraph and see how much performance gain we get.
        // the implication: (&& ?a ?b) ==> (|| ?a ?c)

        // This is a ruleset of baseline implications.
        // We should think kind of hard about how we can synthesize rules like this instead
        // of hard-coding them.
        // The tricky bit is the inductive case -- it's not just finding single-step implications;
        // but rather depends on a "star-step" like transitive closure thing.
        // So, I don't really know how you would find something like this in an e-graph.
        egraph.parse_and_run_program(None,
            r#"
            (rewrite
                (And ?a ?b)
                (And ?b ?a)
                :ruleset find-path)
            
            (rewrite
                (Or ?a ?b)
                (Or ?b ?a)
                :ruleset find-path)

            ;;; the base cases.
            (rule
                ((And ?a ?b))
                ((edge (And ?a ?b) ?a)
                 (edge (And ?a ?b) ?b))
                :ruleset find-path)

            (rule
                ((Or ?a ?b))
                ((edge (Or ?a ?b) ?a)
                 (edge (Or ?a ?b) ?b))
                :ruleset find-path)

            ;;; the inductive cases.
            (rule
                ((And ?a ?b)
                 (path ?a ?c))
                ((path (And ?a ?b) ?c))
                :ruleset find-path)

            (rule
                ((Or ?a ?b)
                 (path ?c ?a))
                ((path ?c (Or ?a ?b)))
                :ruleset find-path)

            (rule
                ((And ?a ?b)
                 (And ?c ?d)
                 (path ?a ?c)
                 (path ?b ?d))
                ((path (And ?a ?b) (And ?c ?d)))
                :ruleset find-path)

            "#).unwrap();


        // 3. add the lhs, rhs of each implication to the egraph
        // now, attempt to derive the selected implications.
        // step 2
        for imp in imps.iter().chain(chosen.iter()) {
            let lhs = egg_to_egglog(&enumo::Sexp::from_str(&Pred::instantiate(&imp.lhs).to_string()).unwrap());
            let rhs = egg_to_egglog(&enumo::Sexp::from_str(&Pred::instantiate(&imp.rhs).to_string()).unwrap());

            // add lhs, rhs to egraph
            add_term(&mut egraph, &lhs);
            add_term(&mut egraph, &rhs);
            // egraph.parse_and_run_program(None, &lhs.to_string()).unwrap();
            // egraph.parse_and_run_program(None, &rhs.to_string()).unwrap();
        }

        // step 3
        egraph.parse_and_run_program(None, "(run-schedule (saturate find-path))").unwrap();

        let mut keep = vec![];

        // step 4
        for imp in imps {
            let lhs = egg_to_egglog(&enumo::Sexp::from_str(&Pred::instantiate(&imp.lhs).to_string()).unwrap());
            let rhs = egg_to_egglog(&enumo::Sexp::from_str(&Pred::instantiate(&imp.rhs).to_string()).unwrap());


            if !egraph.parse_and_run_program(None,
                format!("(check (path {} {}))", lhs, rhs).as_str()).is_ok() {
                // the path does not exist
                keep.push(imp.clone());
            } else {
                println!("discarding: {}", imp.name);
            }

        }

    keep
}

#[test]
fn validate() {
    let validation = validate_implication(Implication {
         name: "test".into(),
         lhs: "(<= ?a ?b)".parse().unwrap(),
         rhs: "(|| (< ?a ?b) (== ?a ?b))".parse().unwrap(),
    });

    println!("validation result: {:?}", validation);

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
    // This kind of sucks, but we need to re-add the Halide language definition to the egraph.
    // TODO: @ninehusky: later, as with `validate_implication`, we should move this to the `SynthLanguage` trait.
    let pred_defn = r#"
    (datatype Predicate)
    (constructor Lit (i64) Predicate)
    (constructor Abs (Predicate) Predicate)
    (constructor Lt (Predicate Predicate) Predicate)
    (constructor Leq (Predicate Predicate) Predicate)
    (constructor Gt (Predicate Predicate) Predicate)
    (constructor Geq (Predicate Predicate) Predicate)
    (constructor Eq (Predicate Predicate) Predicate)
    (constructor Neq (Predicate Predicate) Predicate)
    (constructor Implies (Predicate Predicate) Predicate)
    (constructor Not (Predicate) Predicate)
    (constructor Neg (Predicate) Predicate)
    (constructor And (Predicate Predicate) Predicate)
    (constructor Or (Predicate Predicate) Predicate)
    (constructor Xor (Predicate Predicate) Predicate)
    (constructor Add (Predicate Predicate) Predicate)
    (constructor Sub (Predicate Predicate) Predicate)
    (constructor Mul (Predicate Predicate) Predicate)
    (constructor Div (Predicate Predicate) Predicate)
    (constructor Mod (Predicate Predicate) Predicate)
    (constructor Min (Predicate Predicate) Predicate)
    (constructor Max (Predicate Predicate) Predicate)
    (constructor Select (Predicate Predicate Predicate) Predicate)
    (constructor Var (String) Predicate)
    "#;

    egraph.parse_and_run_program(None, pred_defn).unwrap();

    egraph.parse_and_run_program(None,
        r#"
        (relation edge (Predicate Predicate))
        (relation path (Predicate Predicate))

        (ruleset find-path)

        ;;; The base case.
        ;;; (would be great to have (edge x x) for all x, but no way to
        ;;;  specify rule that is essentially "match on everything".)
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
fn shrink_implications_halide_step() {
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
fn shrink_implications_halide_path() {
    // we have:
    // (&& ?a ?b) ==> ?a
    // ?a ==> (|| ?a ?c)
    // therefore, given the following two implications:
    // (> a b) ==> (>= a b)
    // (&& (> a b) (>= a c)) ==> (>= a b)
    // we should only keep the first one.

    let imps: Vec<Implication<Pred>> = vec![
        Implication {
            name: "(> a b) ==> (>= a b)".into(),
            lhs: "(> a b)".parse().unwrap(),
            rhs: "(>= a b)".parse().unwrap(),
        },
        Implication {
            name: "(&& (> a b) (>= a c)) ==> (>= a b)".into(),
            lhs: "(&& (> a b) (>= a c))".parse().unwrap(),
            rhs: "(>= a b)".parse().unwrap(),
        },
    ];

    let mut imps = imps.clone();
    let (new_imps, invalid) = minimize_implications(&mut imps, &mut vec![]);
    assert_eq!(invalid.len(), 0);
    assert_eq!(new_imps.len(), 1);

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
