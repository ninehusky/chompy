use egglog::{util::IndexMap, EGraph};
use enumo::Sexp;
use ruler::*;
use std::{collections::HashSet, str::FromStr};

const CVEC_LEN: usize = 1000;

type Constant = Option<i64>;

#[derive(Debug)]
struct Rule {
    condition: Option<Sexp>,
    lhs: Sexp,
    rhs: Sexp,
}

struct Rules {
    non_conditional: Vec<Rule>,
    conditional: Vec<Rule>,
}

fn cvec_match(
    eclass_term_map: &HashMap<i64, Sexp>,
    term_to_cvec_map: &HashMap<String, Vec<Constant>>,
    mask_to_preds: &HashMap<Vec<bool>, HashSet<String>>,
) -> Rules {
    let mut result = Rules {
        non_conditional: vec![],
        conditional: vec![],
    };
    let ec_keys = eclass_term_map.keys().into_iter();
    for i in 0..ec_keys.len() {
        for j in i + 1..ec_keys.len() {
            // TODO: check if we merged these in an earlier step

            let ec1 = ec_keys.clone().nth(i).unwrap();
            let ec2 = ec_keys.clone().nth(j).unwrap();
            let term1 = eclass_term_map.get(ec1).unwrap();
            let term2 = eclass_term_map.get(ec2).unwrap();
            // TODO: @ninehusky: re-implement the memoization stuff
            let cvec1 = get_cvec(&term1.to_string());
            let cvec2 = get_cvec(&term2.to_string());

            if cvec1.iter().all(|x| x.is_none()) && cvec2.iter().all(|x| x.is_none()) {
                // prune cvecs which don't really matter
                continue;
            }

            if cvec1 == cvec2 {
                result.non_conditional.push(Rule {
                    condition: None,
                    lhs: term1.clone(),
                    rhs: term2.clone(),
                });
                result.non_conditional.push(Rule {
                    condition: None,
                    lhs: term2.clone(),
                    rhs: term1.clone(),
                });
            } else {
                let mut has_meaningful_diff = false;
                let mut same_vals: Vec<bool> = vec![];
                for (cvec_1_el, cvec_2_el) in cvec1.iter().zip(cvec2.iter()) {
                    if cvec_1_el != cvec_2_el {
                        if cvec_1_el.is_some() || cvec_2_el.is_some() {
                            has_meaningful_diff = true;
                        }
                    }
                    same_vals.push(cvec_1_el == cvec_2_el);
                }

                if !has_meaningful_diff {
                    continue;
                }

                // get the number of things that match
                let matching_count = same_vals.iter().filter(|&x| *x).count();

                if matching_count < 2 {
                    continue;
                }

                if let Some(preds) = mask_to_preds.get(&same_vals) {
                    for pred in preds {
                        result.conditional.push(Rule {
                            condition: Some(Sexp::from_str(pred).unwrap()),
                            lhs: term1.clone(),
                            rhs: term2.clone(),
                        });
                        result.conditional.push(Rule {
                            condition: Some(Sexp::from_str(pred).unwrap()),
                            lhs: term2.clone(),
                            rhs: term1.clone(),
                        });
                    }
                }
            }
        }
    }
    result
}

fn get_eclass_term_map(egraph: &mut EGraph) -> HashMap<i64, Sexp> {
    let mut outputs = egraph
        .parse_and_run_program(None, r#"(push)(run eclass-report 20)(pop)"#)
        .unwrap()
        .into_iter()
        .peekable();

    let mut map = HashMap::default();

    while outputs.peek().is_some() {
        outputs.next().unwrap();
        let eclass = outputs.next().unwrap().to_string().parse::<i64>().unwrap();
        outputs.next().unwrap();
        let term = outputs.next().unwrap();
        map.insert(eclass, Sexp::from_str(&term).unwrap());
    }
    map
}

fn get_cvec(term: &str) -> Vec<Constant> {
    let cvec_sexp = ruler::enumo::Sexp::from_str(term).unwrap();
    match cvec_sexp {
        Sexp::Atom(_) => {
            panic!("uhh");
        }
        Sexp::List(ref l) => {
            let op = l[0].to_string();
            match op.as_str() {
                "Num" => {
                    assert!(l.len() == 2);
                    let num = l[1].to_string().parse::<i64>().unwrap();
                    return vec![Some(num); CVEC_LEN];
                }
                "Var" => {
                    assert!(l.len() == 2);
                    // get range centered at 0 of length CVEC_LEN
                    let cvec_len_as_i64 = CVEC_LEN as i64;
                    return (-cvec_len_as_i64 / 2..cvec_len_as_i64 / 2)
                        .map(|x| Some(x))
                        .collect::<Vec<_>>();
                }
                "MathOp1" => {
                    assert!(l.len() == 3);
                    let op = l[1].to_string();
                    let x = get_cvec(&l[2].to_string());
                    let mut result = vec![];
                    for x_el in x.iter() {
                        result.push({
                            if x_el.is_none() {
                                None
                            } else {
                                match op.as_str() {
                                    "(Abs )" => x_el.unwrap().checked_abs(),
                                    _ => unreachable!("uhh"),
                                }
                            }
                        });
                    }
                    return result;
                }
                "MathOp2" => {
                    assert!(l.len() == 4);
                    let op = l[1].to_string();
                    let x = get_cvec(&l[2].to_string());
                    let y = get_cvec(&l[3].to_string());
                    let mut result = vec![];
                    for (x_el, y_el) in x.iter().zip(y.iter()) {
                        result.push({
                            if x_el.is_none() || y_el.is_none() {
                                None
                            } else {
                                match op.as_str() {
                                    "(Add )" => x_el.unwrap().checked_add(y_el.unwrap()),
                                    "(Sub )" => x_el.unwrap().checked_sub(y_el.unwrap()),
                                    "(Mul )" => x_el.unwrap().checked_mul(y_el.unwrap()),
                                    "(Div )" => x_el.unwrap().checked_div(y_el.unwrap()),
                                    _ => unreachable!("received op: {}", op),
                                }
                            }
                        });
                    }
                    return result;
                }
                _ => unreachable!(),
            }
        }
    }
}

fn get_pred_cvec(term: &str) -> Vec<bool> {
    let sexp = Sexp::from_str(term).unwrap();
    let mut cvec = vec![];
    match sexp {
        Sexp::Atom(_) => {
            panic!("uhh");
        }
        Sexp::List(ref l) => {
            let op = l[0].to_string();
            match op.as_str() {
                "PredOp2" => {
                    assert!(l.len() == 4);
                    let op = l[1].to_string();
                    let x = get_cvec(&l[2].to_string());
                    let y = get_cvec(&l[3].to_string());
                    let my_fn = match op.as_str() {
                        "(Eq )" => i64::eq,
                        "(Neq )" => i64::ne,
                        "(Gt )" => i64::gt,
                        "(Ge )" => i64::ge,
                        "(Lt )" => i64::lt,
                        _ => unreachable!(),
                    };
                    for (x_el, y_el) in x.iter().zip(y.iter()) {
                        cvec.push(my_fn(&x_el.unwrap(), &y_el.unwrap()));
                    }
                    cvec
                }
                _ => unreachable!(),
            }
        }
    }
}

fn get_pred_to_cvec(
    _egraph: &mut EGraph,
    new_terms: enumo::Workload,
    map: &mut HashMap<Vec<bool>, HashSet<String>>,
) -> Result<(), String> {
    // generate a bunch of stuff.
    let productions = enumo::Workload::new(&["(PredOp2 predop x y)"])
        .plug(
            "predop",
            &enumo::Workload::new(&["(Eq)", "(Neq)", "(Gt)", "(Ge)", "(Lt)"]),
        )
        .plug("x", &new_terms)
        .plug("y", &new_terms);

    for term in productions.force().into_iter() {
        let cvec = get_pred_cvec(&term.to_string());
        // if all are true or all are false, discard.
        if cvec.iter().all(|&x| x) || cvec.iter().all(|&x| !x) {
            continue;
        }
        // add to map
        map.entry(cvec.clone())
            .or_insert(HashSet::default())
            .insert(term.to_string());
    }

    Ok(())
}

fn add_predicates_to_egraph(
    egraph: &mut EGraph,
    mask_to_preds: &HashMap<Vec<bool>, HashSet<String>>,
) {
    for (_, preds) in mask_to_preds {
        let mut add_preds_prog = String::new();
        let original_pred = preds.iter().nth(0).unwrap().to_string();
        for (i, pred) in preds.iter().enumerate() {
            add_preds_prog += format!(
                r#"
            {pred}
            (union {pred} {original_pred})
            "#
            )
            .replace("quote", "\"")
            .as_str();
        }
        egraph.parse_and_run_program(None, &add_preds_prog).unwrap();
    }
}

#[test]
fn math_eval() {
    const MAX_DEPTH: usize = 1;
    let mut egraph = egglog::EGraph::default();
    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype MathFn
          (Add)
          (Sub)
          (Mul)
          (Div)
          (Abs))

        (datatype Math
          (Num i64)
          (Var String)
          (MathOp1 MathFn Math)
          (MathOp2 MathFn Math Math))

        (datatype PredFn
          (Eq)
          (Neq)
          (Gt)
          (Ge)
          (Lt))

        (datatype Pred
          (PredOp2 PredFn Math Math))

        (relation cond-equal (Pred Math Math))

        (function eclass (Math) i64 :merge (min old new))

        (ruleset eclass-report)
        (ruleset non-cond-rewrites)
        (ruleset cond-rewrites)

        (rule
          ((eclass ?math))
          ((extract "eclass:")
           (extract (eclass ?math))
           (extract "candidate term:")
           (extract ?math))
           :ruleset eclass-report)
        "#,
        )
        .unwrap();

    let atoms = enumo::Workload::new(&["(Num 0)", "(Num 1)", "(Var quoteaquote)"]);

    // we probably won't need this; cvecs kind of serve as a good enough approximation
    // of an eclass.
    let mut pred_egraph = egglog::EGraph::default();
    let mut mask_to_preds = HashMap::default();
    get_pred_to_cvec(&mut pred_egraph, atoms.clone(), &mut mask_to_preds).unwrap();

    add_predicates_to_egraph(&mut egraph, &mask_to_preds);

    let unary_fns = enumo::Workload::new(&["(Abs)"]);
    let binary_fns = enumo::Workload::new(&["(Add)", "(Sub)", "(Mul)", "(Div)"]);

    let term_productions = enumo::Workload::new(&["(MathOp2 mathop x y)", "(MathOp1 unaryop x)"])
        .plug("mathop", &binary_fns)
        .plug("unaryop", &unary_fns)
        .plug("x", &atoms)
        .plug("y", &atoms);

    // empty map
    let mut eclass_to_term_map = get_eclass_term_map(&mut egraph);

    let mut last_term_set = atoms;

    let mut term_cvec_map: HashMap<String, Vec<Constant>> = HashMap::default();

    for i in 0..MAX_DEPTH {
        let new_term_set = enumo::Workload::new(&[
            "(MathOp2 mathop x y)",
            "(MathOp1 unaryop x)",
            "(Var quoteaquote)",
            "(Num 0)",
            "(Num 1)",
        ])
        .clone()
        .plug("mathop", &binary_fns)
        .plug("unaryop", &unary_fns)
        .plug("x", &last_term_set)
        .plug("y", &last_term_set);
        let mut add_terms_prog: String = String::new();

        // add new terms to the egraph.
        let num_eclasses = eclass_to_term_map.keys().len();
        for (i, term) in new_term_set.force().into_iter().enumerate() {
            let term_str = term.to_string().replace("quote", "\"");
            let cvec = get_cvec(&term_str);
            // remove whitespace
            term_cvec_map.insert(term_str.replace(" ", "").replace("\"", ""), cvec);
            let eclass = num_eclasses + i;
            add_terms_prog += format!(
                r#"
              {term_str}
              (set (eclass {term_str}) {eclass})
                "#,
            )
            .as_str();
        }

        egraph.parse_and_run_program(None, &add_terms_prog).unwrap();

        // attempt to merge terms with current rules
        egraph
            .parse_and_run_program(None, "(run non-cond-rewrites 100)")
            .unwrap();

        egraph
            .parse_and_run_program(None, "(run cond-rewrites 100)")
            .unwrap();

        // get representative terms for each NEW eclass.
        eclass_to_term_map = get_eclass_term_map(&mut egraph);

        // perform cvec matching
        let rules = cvec_match(&eclass_to_term_map, &term_cvec_map.clone(), &mask_to_preds);

        for rule in rules.non_conditional {
            // println!("{} ~> {}", rule.lhs.to_string(), rule.rhs.to_string());

            let lhs = rule.lhs.to_string();
            let rhs = rule.rhs.to_string();

            let prog = r#"
            (rewrite {lhs} {rhs} :ruleset non-cond-rewrites)"#
                .replace("{lhs}", &lhs.replace(" a ", "\"a\""))
                .replace("{rhs}", &rhs.replace(" a ", "\"a\""));
            // add the rules
            egraph.parse_and_run_program(None, &prog).unwrap();
        }

        for rule in rules.conditional {
            let conditional = rule.condition.unwrap().to_string();
            let lhs = rule.lhs.to_string();
            let rhs = rule.rhs.to_string();
            let cond_equal_statement = r#"
                (cond-equal {conditional} {lhs} {rhs})
            "#
            .replace(
                "{conditional}",
                &conditional.replace("quoteaquote", "\"a\""),
            )
            .replace("{lhs}", &lhs.replace(" a ", "\"a\""))
            .replace("{rhs}", &rhs.replace(" a ", "\"a\""));

            let already_inside =
                egraph.parse_and_run_program(None, r#"(extract {cond_equal_statement})"#);

            if already_inside.is_ok() {
                continue;
            }
            egraph
                .parse_and_run_program(None, &cond_equal_statement)
                .unwrap();
            // println!("if {} then {} ~> {}", conditional, lhs, rhs);
        }

        egraph
            .parse_and_run_program(None, "(run non-cond-rewrites 100)")
            .unwrap();
        last_term_set = new_term_set;
    }

    egraph
        .parse_and_run_program(None, "(run eclass-report 20)")
        .unwrap();

    // check that we can find rule:
    // if a != 0 then a / a = 1
    egraph
        .parse_and_run_program(None,
            "(check (cond-equal (PredOp2 (Neq) (Var \"a\") (Num 0)) (MathOp2 (Div) (Var \"a\") (Var \"a\")) (Num 1)))")
        .unwrap();

    // if a >= 0 then abs(a) = a
    egraph
        .parse_and_run_program(None,
            "(check (cond-equal (PredOp2 (Ge) (Var \"a\") (Num 0)) (MathOp1 (Abs) (Var \"a\")) (Var \"a\")))")
        .unwrap();

    // check we didn't include a bad rule:
    // if a < 1 then abs(a) = a
    egraph
        .parse_and_run_program(None,
            "(fail (check (cond-equal (PredOp2 (Lt) (Var \"a\") (Num 1)) (MathOp1 (Abs) (Var \"a\")) (Var \"a\"))))")
        .unwrap();

    // dummy non-conditional equality check
    egraph
        .parse_and_run_program(
            None,
            "(check (= (eclass (Num 1)) (eclass (MathOp2 (Div) (Num 1) (Num 1)))))",
        )
        .unwrap();
}
