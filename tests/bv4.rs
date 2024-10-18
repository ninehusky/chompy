use chompy::Chomper;
use rand::{rngs::StdRng, Rng, SeedableRng};
use ruler::{
    enumo::{Sexp, Workload},
    HashMap, HashSet, ValidationResult,
};

use chompy::Rule;

use egglog::EGraph;

use std::str::FromStr;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Bitvector {
    pub width: u64,
    pub value: u64,
}

const MAX_BITWIDTH: usize = 4;
const CVEC_LEN: usize = 6;

pub struct BitvectorChomper {
    pub value_env: HashMap<String, Vec<u64>>,
    pub term_memo: HashMap<String, Vec<Option<Bitvector>>>,
    pub pred_memo: HashMap<String, Vec<bool>>,
    pub rng: StdRng,
}

impl BitvectorChomper {
    // stupid. see #2.
    fn make_string_not_bad(term: &str, env: &HashMap<String, Vec<u64>>) -> String {
        let mut term_string = term.to_string();
        for (var, _) in env {
            term_string = term_string.replace(&format!(" {} ", var), &format!(" \"{}\" ", var));
        }
        term_string
    }

    fn add_rewrite(&mut self, egraph: &mut EGraph, lhs: Sexp, rhs: Sexp) {
        let term1 =
            BitvectorChomper::make_string_not_bad(lhs.to_string().as_str(), &self.value_env);
        let term2 =
            BitvectorChomper::make_string_not_bad(rhs.to_string().as_str(), &self.value_env);
        egraph
            .parse_and_run_program(
                None,
                format!(
                    r#"
            (union {term1} {term2})
            "#
                )
                .as_str(),
            )
            .unwrap();
    }

    fn add_conditional_rewrite(&mut self, egraph: &mut EGraph, cond: Sexp, lhs: Sexp, rhs: Sexp) {
        let pred =
            BitvectorChomper::make_string_not_bad(cond.to_string().as_str(), &self.value_env);
        let term1 =
            BitvectorChomper::make_string_not_bad(lhs.to_string().as_str(), &self.value_env);
        let term2 =
            BitvectorChomper::make_string_not_bad(rhs.to_string().as_str(), &self.value_env);
        egraph
            .parse_and_run_program(
                None,
                format!(
                    r#"
                    (cond-equal {pred} {term1} {term2})
                    (cond-equal {pred} {term2} {term1})
            "#
                )
                .as_str(),
            )
            .unwrap();
    }

    fn add_predicates_to_egraph(
        &mut self,
        egraph: &mut EGraph,
        preds: Workload,
    ) -> HashMap<Vec<bool>, HashSet<String>> {
        let mut map = HashMap::default();
        for pred in preds.force() {
            let pred_str =
                BitvectorChomper::make_string_not_bad(pred.to_string().as_str(), &self.value_env);
            let mask = self.interpret_pred(&pred);
            map.entry(mask.clone())
                .or_insert(HashSet::default())
                .insert(pred_str.clone());

            egraph
                .parse_and_run_program(
                    None,
                    format!(
                        r#"
                    {pred_str}
                    "#
                    )
                    .as_str(),
                )
                .unwrap();
        }
        map
    }
}

impl Chomper for BitvectorChomper {
    type Constant = Bitvector;
    fn interpret_term(&mut self, term: &ruler::enumo::Sexp) -> chompy::CVec<Self> {
        interpret_term_internal(term.clone(), &self.value_env, &mut self.term_memo)
    }

    fn interpret_pred(&mut self, pred: &ruler::enumo::Sexp) -> Vec<bool> {
        interpret_pred_internal(pred.clone(), &self.value_env, &mut self.pred_memo)
    }

    // hehe
    fn validate_rule(&self, _rule: chompy::Rule) -> ValidationResult {
        ValidationResult::Valid
    }

    fn make_preds(&self) -> Workload {
        Workload::new(&[r#"(PredOp2 (Le) (ValueVar "r") (ValueVar "p"))"#])
    }

    fn make_terms(&self, old_terms: &ruler::enumo::Workload) -> ruler::enumo::Workload {
        let productions = Workload::new(&[
            "(BVOp1 BVValue unop BVTerm)",
            "(BVOp2 BVValue binop BVTerm BVTerm)",
        ])
        .plug("binop", &Workload::new(&["(Add)", "(Mul)", "(Shr)"]))
        .plug("unop", &Workload::new(&["(Neg)", "(Not)"]))
        .plug("BVTerm", old_terms)
        // width for the root expression
        .plug(
            "BVValue",
            &Workload::new(&["(ValueVar p)", "(ValueVar r)", "(ValueVar q)"]),
        );
        productions
    }
}

impl Bitvector {
    fn new(width: u64, value: u64) -> Self {
        if width > MAX_BITWIDTH as u64 {
            panic!(
                "error: constructing bitvector with width {} that is greater than {}",
                width, MAX_BITWIDTH
            );
        }
        if value > (1 << width) {
            // println!(
            //     "warning: constructing bitvector with value {} that is greater than 2^{}",
            //     value, width
            // );
        }
        Bitvector {
            width,
            value: value % (1 << width),
        }
    }
}

fn initialize_value_env(
    rng: &mut StdRng,
    vars: Vec<String>,
    min: u64,
    max: u64,
) -> HashMap<String, Vec<u64>> {
    let mut env: HashMap<String, Vec<u64>> = HashMap::default();
    for var in vars {
        if max - min < CVEC_LEN as u64 {
            // make vector from min to max, repeat it and take CVEC_LEN elements.
            let mut vals: Vec<u64> = vec![];
            while vals.len() < CVEC_LEN {
                let value: u64 = rng.gen_range(min..max);
                vals.push(value);
            }
            env.insert(var, vals);
        } else {
            let mut unique_vals: HashSet<u64> = HashSet::default();
            while unique_vals.len() < CVEC_LEN {
                let value: u64 = rng.gen_range(min..max);
                unique_vals.insert(value);
            }
            env.insert(var, unique_vals.into_iter().collect());
        }
    }
    env
}

fn interpret_pred_internal(
    pred: Sexp,
    value_env: &HashMap<String, Vec<u64>>,
    pred_memo: &mut HashMap<String, Vec<bool>>,
) -> Vec<bool> {
    if let Some(result) = pred_memo.get(&pred.to_string()) {
        return result.clone();
    }
    match pred {
        Sexp::List(l) => match l[0].to_string().as_str() {
            "PredOp2" => {
                assert!(l.len() == 4);
                let first_vvec = get_value_vec(l[2].clone(), value_env);
                let second_vvec = get_value_vec(l[3].clone(), value_env);
                let op = match &l[1] {
                    Sexp::List(l) => match &l[0] {
                        Sexp::Atom(op) => match op.as_str() {
                            "Eq" => |(a, b)| a == b,
                            "Neq" => |(a, b)| a != b,
                            "Le" => |(a, b)| a <= b,
                            "Ge" => |(a, b)| a >= b,
                            // "Lt" => |(a, b)| a < b,
                            // "Gt" => |(a, b)| a > b,
                            _ => panic!("unknown pred operator {:?}", l[1].to_string()),
                        },
                        _ => panic!(),
                    },
                    _ => panic!("pred operator should be an atom, but found {:?}", l[1]),
                };
                first_vvec.iter().zip(second_vvec.iter()).map(op).collect()
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
}

fn get_value_vec(value: Sexp, value_env: &HashMap<String, Vec<u64>>) -> Vec<u64> {
    match value {
        Sexp::List(l) => match l[0].to_string().as_str() {
            "ValueVar" => {
                assert!(l.len() == 2);
                let value = value_env.get(&l[1].to_string()).unwrap();
                return value.clone();
            }
            "ValueNum" => {
                assert!(l.len() == 2);
                let value = l[1].to_string().parse::<u64>();
                vec![value.unwrap(); CVEC_LEN]
            }
            _ => panic!("unknown value operator {:?}", l[0].to_string()),
        },
        _ => panic!("value should be a list, but found {:?}", value),
    }
}

fn interpret_term_internal(
    term: ruler::enumo::Sexp,
    value_env: &HashMap<String, Vec<u64>>,
    memo: &mut HashMap<String, Vec<Option<Bitvector>>>,
) -> Vec<Option<Bitvector>> {
    if let Some(result) = memo.get(&term.to_string()) {
        return result.clone();
    }
    let cvec: Vec<Option<Bitvector>> = match term {
        Sexp::Atom(atom) => {
            panic!("You should not be interpreting mii: {:?}", atom);
        }
        Sexp::List(ref l) => {
            let op = l[0].to_string();
            match op.as_str() {
                "Bitvector" => {
                    let widths = get_value_vec(l[1].clone(), value_env);
                    let values = get_value_vec(l[2].clone(), value_env);
                    widths
                        .iter()
                        .zip(values.iter())
                        .map(|(width, value)| Some(Bitvector::new(*width, *value)))
                        .collect()
                }
                "BVOp1" => {
                    assert!(l.len() == 4);
                    let widths = get_value_vec(l[1].clone(), value_env);
                    let op = l[2].clone();
                    fn f(a: u64, op: &Sexp) -> Option<u64> {
                        match op {
                            Sexp::List(l) => {
                                assert!(l.len() == 1);
                                match l[0] {
                                    Sexp::Atom(ref op) => match op.as_str() {
                                        "Neg" => Some(a.overflowing_neg().0),
                                        "Not" => Some(if a == 0 { 1 } else { 0 }),
                                        _ => todo!("not implemented {:?}", op),
                                    },
                                    _ => panic!("expected atom, found {:?}", op),
                                }
                            }
                            _ => panic!("expected list, found {:?}", op),
                        }
                    }
                    let child_cvecs: Vec<Vec<Option<Bitvector>>> = l[3..4]
                        .iter()
                        .map(|x| interpret_term_internal(x.clone(), value_env, memo))
                        .into_iter()
                        .collect();

                    child_cvecs[0]
                        .iter()
                        .zip(widths.iter())
                        .map(|(first_child_val, width)| match first_child_val {
                            Some(first_child) => {
                                let result = f(first_child.value, &op);
                                match result {
                                    Some(result) => Some(Bitvector::new(*width, result)),
                                    None => None,
                                }
                            }
                            _ => None,
                        })
                        .collect()
                }
                "BVOp2" => {
                    assert!(l.len() == 5);
                    let widths = get_value_vec(l[1].clone(), value_env);
                    let op = l[2].clone();
                    // TODO: @ninehusky - macroify this f thing
                    fn f(a: u64, b: u64, op: &Sexp) -> Option<u64> {
                        match op {
                            Sexp::Atom(op) => panic!("expected list, found atom {:?}", op),
                            Sexp::List(l) => {
                                assert!(l.len() == 1);
                                match l[0] {
                                    Sexp::Atom(ref op) => match op.as_str() {
                                        "Add" => Some(a.overflowing_add(b).0),
                                        "Sub" => Some(a.overflowing_sub(b).0),
                                        "Mul" => Some(a.overflowing_mul(b).0),
                                        "Shl" => Some(a.overflowing_shl(b as u32).0),
                                        "Shr" => Some(a.overflowing_shr(b as u32).0),
                                        "Lt" => Some(if a < b { 1 } else { 0 }),
                                        "Gt" => Some(if a > b { 1 } else { 0 }),
                                        _ => todo!("not implemented {:?}", op),
                                    },
                                    _ => panic!("expected atom, found {:?}", op),
                                }
                            }
                        }
                    }
                    let child_cvecs: Vec<Vec<Option<Bitvector>>> = l[3..5]
                        .iter()
                        .map(|x| interpret_term_internal(x.clone(), value_env, memo))
                        .into_iter()
                        .collect();

                    child_cvecs[0]
                        .iter()
                        .zip(child_cvecs[1].iter())
                        .zip(widths.iter())
                        .map(|((first_child_val, second_child_val), width)| {
                            match (first_child_val, second_child_val) {
                                (Some(first_child), Some(second_child)) => {
                                    let result = f(first_child.value, second_child.value, &op);
                                    match result {
                                        Some(result) => Some(Bitvector::new(*width, result)),
                                        None => None,
                                    }
                                }
                                _ => None,
                            }
                        })
                        .collect()
                }
                _ => panic!(
                    "found weird operator {:?} in term {:?}",
                    op.as_str(),
                    term.to_string()
                ),
            }
        }
    };
    memo.insert(term.to_string(), cvec.clone());
    cvec
}

#[test]
pub fn run_bv4_eval() {
    let mut egraph = egglog::EGraph::default();
    egraph
        .parse_and_run_program(
            Some("./egglog/bv4.egg".to_string()),
            include_str!("./egglog/bv4.egg"),
        )
        .unwrap();

    let extraction = egraph
        .parse_and_run_program(
            None,
            r#"
        ;;; keep the lowest bit
        (let expr0 (BVOp2 (ValueNum 2) (Add) (Bitvector (ValueNum 3) (ValueVar "x")) (Bitvector (ValueNum 3) (ValueNum 2))))
        (extract expr0)
        "#,
        )
        .unwrap();

    let mut rng = StdRng::seed_from_u64(0xdeadbeef);

    let value_env =
        initialize_value_env(&mut rng, vec!["x".to_string()], 0, (1 << MAX_BITWIDTH) - 1);
    let width_env = initialize_value_env(
        &mut rng,
        vec!["p".to_string(), "q".to_string(), "r".to_string()],
        1,
        MAX_BITWIDTH as u64,
    );
    // intersect the maps.
    let value_env: HashMap<String, Vec<u64>> = value_env
        .into_iter()
        .chain(width_env.into_iter())
        .collect::<HashMap<String, Vec<u64>>>();
    let cvec = interpret_term_internal(
        Sexp::from_str(extraction[0].as_str()).unwrap(),
        &value_env,
        &mut HashMap::default(),
    );
}

#[test]
pub fn test_bv4_new_flow() {
    let mut egraph = egglog::EGraph::default();
    egraph
        .parse_and_run_program(
            Some("./egglog/bv4.egg".to_string()),
            include_str!("./egglog/bv4.egg"),
        )
        .unwrap();
    let atoms = Workload::new(&[
        r#"(Bitvector (ValueVar "p") (ValueVar "x"))"#,
        r#"(Bitvector (ValueVar "q") (ValueVar "y"))"#,
        r#"(Bitvector (ValueNum 2) (ValueNum 1))"#,
        r#"(Bitvector (ValueNum 2) (ValueNum 2))"#,
    ]);
    let mut rng = StdRng::seed_from_u64(0xdeadbeef);
    let value_env = initialize_value_env(
        &mut rng,
        vec!["x".to_string(), "y".to_string()],
        0,
        (1 << MAX_BITWIDTH) - 1,
    );
    let width_env = initialize_value_env(
        &mut rng,
        vec!["p".to_string(), "q".to_string(), "r".to_string()],
        1,
        MAX_BITWIDTH as u64,
    );
    let value_env: HashMap<String, Vec<u64>> = value_env
        .into_iter()
        .chain(width_env.into_iter())
        .collect::<HashMap<String, Vec<u64>>>();

    let mut chomper = BitvectorChomper {
        value_env,
        term_memo: HashMap::default(),
        pred_memo: HashMap::default(),
        rng: StdRng::seed_from_u64(0xdeadbeef),
    };

    let new_workload = chomper.make_terms(&atoms).force();

    let mut max_eclass_id = 0;

    const MAX_ITERATIONS: usize = 100;
    let mut good = false;
    for _ in 0..MAX_ITERATIONS {
        if good {
            break;
        }
        for term in &new_workload {
            // stupid. see #2.
            let term_string = BitvectorChomper::make_string_not_bad(
                term.to_string().as_str(),
                &chomper.value_env,
            );
            egraph
                .parse_and_run_program(
                    None,
                    format!(
                        r#"
                {term_string}
                (set (eclass {term_string}) {max_eclass_id})
                "#
                    )
                    .as_str(),
                )
                .unwrap();
            max_eclass_id += 1;
        }
        let vals = chomper.cvec_match(&mut egraph, &HashMap::default());
        // for val in &vals.non_conditional {
        //     println!("{:?} ~> {:?}", val.lhs.to_string(), val.rhs.to_string());
        // }
        chomper.get_eclass_term_map(&mut egraph);
        // let serialized = egraph.serialize(egglog::SerializeConfig::default());
        // serialized.to_svg_file("bv4.svg").unwrap();

        if vals.non_conditional.contains(&Rule {
            condition: None,
            lhs: Sexp::from_str("(BVOp2 (ValueVar p) (Shl) (Bitvector (ValueVar q) (ValueVar y)) (Bitvector (ValueNum 2) (ValueNum 1)))").unwrap(),
            rhs: Sexp::from_str("(BVOp2 (ValueVar p) (Mul) (Bitvector (ValueVar q) (ValueVar y)) (Bitvector (ValueNum 2) (ValueNum 2)))").unwrap(),
        }) {
            good = true;
            break;
        }
    }
    assert!(good);
}

#[test]
pub fn bv4_neg_not() {
    let mut egraph = egglog::EGraph::default();
    egraph
        .parse_and_run_program(
            Some("./egglog/bv4.egg".to_string()),
            include_str!("./egglog/bv4.egg"),
        )
        .unwrap();
    let atoms = Workload::new(&[
        r#"(Bitvector (ValueVar "p") (ValueVar "a"))"#,
        r#"(Bitvector (ValueNum 1) (ValueNum 1))"#,
    ]);
    let mut rng = StdRng::seed_from_u64(0xdeadbeef);
    let value_env =
        initialize_value_env(&mut rng, vec!["a".to_string()], 0, (1 << MAX_BITWIDTH) - 1);
    let width_env = initialize_value_env(
        &mut rng,
        vec!["p".to_string(), "q".to_string(), "r".to_string()],
        1,
        MAX_BITWIDTH as u64,
    );
    let value_env: HashMap<String, Vec<u64>> = value_env
        .into_iter()
        .chain(width_env.into_iter())
        .collect::<HashMap<String, Vec<u64>>>();

    let mut chomper = BitvectorChomper {
        value_env,
        term_memo: HashMap::default(),
        pred_memo: HashMap::default(),
        rng: StdRng::seed_from_u64(0xdeadbeef),
    };

    let mut max_eclass_id = 0;

    const MAX_ITERATIONS: usize = 100;
    let mut good = false;
    let mut old_terms = atoms.clone();
    let mut printed_found_first = false;
    let mut printed_found_second = false;
    let mask_to_preds = &chomper.add_predicates_to_egraph(&mut egraph, chomper.make_preds());
    for _ in 0..MAX_ITERATIONS {
        if good {
            break;
        }
        let terms = chomper.make_terms(&old_terms);
        old_terms = terms.clone();

        for term in terms.force() {
            println!("term is {:?}", term.to_string());
            // stupid. see #2.
            let term_string = BitvectorChomper::make_string_not_bad(
                term.to_string().as_str(),
                &chomper.value_env,
            );
            egraph
                .parse_and_run_program(
                    None,
                    format!(
                        r#"
                    {term_string}
                    (set (eclass {term_string}) {max_eclass_id})
                    "#
                    )
                    .as_str(),
                )
                .unwrap();
            max_eclass_id += 1;

            // for val in &vals.conditional {
            //     chomper.add_conditional_rewrite(
            //         &mut egraph,
            //         val.condition.clone().unwrap(),
            //         val.lhs.clone(),
            //         val.rhs.clone(),
            //     );
            // }

            // let serialized = egraph.serialize(egglog::SerializeConfig::default());
            // println!("nodes in egraph: {}", serialized.nodes.len());
            // serialized.to_svg_file("bv4-new.svg").unwrap();
        }
        let vals = chomper.cvec_match(&mut egraph, mask_to_preds);
        for val in &vals.non_conditional {
            chomper.add_rewrite(&mut egraph, val.lhs.clone(), val.rhs.clone());
        }
        egraph
            .parse_and_run_program(
                None,
                r#"
            (run 100)"#,
            )
            .unwrap();

        if !printed_found_first {
            if egraph
                .parse_and_run_program(
                    None,
                    format!(
                        r#"
                    (check (BVOp1 (ValueVar r ) (Neg ) (Bitvector (ValueVar p ) (ValueVar a ) ) ))
                    "#
                    )
                    .as_str(),
                )
                .is_ok()
            {
                println!("found first term");
                printed_found_first = true;
            }
        }

        if egraph
            .parse_and_run_program(
                None,
                format!(
                    r#"
        (check (BVOp1 (ValueVar p ) (Not ) (Bitvector (ValueVar p ) (ValueVar a ) ) ))
        "#
                )
                .as_str(),
            )
            .is_ok()
        {
            println!("found second term");
        }

        if !printed_found_second {
            if egraph
                    .parse_and_run_program(
                        None,
                        format!(
                            r#"
                            (check (BVOp2 (ValueVar r ) (Add ) (BVOp1 (ValueVar p ) (Not ) (Bitvector (ValueVar p ) (ValueVar a ) ) ) (Bitvector (ValueNum 1 ) (ValueNum 1 ) ) ))
                    "#
                        )
                        .as_str(),
                    )
                    .is_ok()
                {
                    println!("found third term");
                    break;
                }
        }

        if vals.conditional.contains(&Rule {
                condition: Some(Sexp::from_str("(PredOp2 (Le ) (ValueVar r ) (ValueVar p ) )").unwrap()),
                lhs: Sexp::from_str("(BVOp1 (ValueVar r ) (Neg ) (Bitvector (ValueVar p ) (ValueVar a ) ) )").unwrap(),
                rhs: Sexp::from_str("(BVOp2 (ValueVar r ) (Add ) (BVOp1 (ValueVar p ) (Not ) (Bitvector (ValueVar p ) (ValueVar a ) ) ) (Bitvector (ValueNum 1 ) (ValueNum 1 ) ) )").unwrap(),
            }) {
                good = true;
                break;
            }
        chomper.get_eclass_term_map(&mut egraph);
    }
    assert!(good);
}
