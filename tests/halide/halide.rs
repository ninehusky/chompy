use chompy::{CVec, Chomper};
use rand::{rngs::StdRng, Rng, SeedableRng};
use ruler::{
    enumo::{Sexp, Workload},
    HashMap, HashSet, ValidationResult,
};

use std::str::FromStr;

use z3::ast::Ast;

use chompy::utils::TERM_PLACEHOLDER;
use num::Zero;

pub const CVEC_LEN: usize = 20;

#[derive(Debug, Clone)]
pub struct HalideChomper {
    // TODO: this might be buggy given new experiment structure.
    pub memo: HashMap<String, CVec<Self>>,
    pub env: ruler::HashMap<String, CVec<Self>>,
}

impl Chomper for HalideChomper {
    type Constant = i64;
    type Value = i64;

    fn make_constant(&self, constant: chompy::Constant<Self>) -> Sexp {
        Sexp::List(vec![
            Sexp::Atom("Lit".to_string()),
            Sexp::Atom(constant.to_string()),
        ])
    }

    fn language_name() -> String {
        "HalideExpr".to_string()
    }

    fn make_var(&self, var: &str) -> Sexp {
        Sexp::List(vec![
            Sexp::Atom("Var".to_string()),
            Sexp::Atom(var.to_string()),
        ])
    }

    fn get_name_from_var(&self, var: &Sexp) -> String {
        match var {
            Sexp::List(l) => {
                assert_eq!(l.len(), 2);
                if let Sexp::Atom(name) = &l[1] {
                    name.clone()
                } else {
                    panic!("Expected atom for variable name, found {:?}", l[1])
                }
            }
            _ => panic!("Expected list for variable, found {:?}", var),
        }
    }

    fn productions(&self) -> ruler::enumo::Workload {
        Workload::new(&[
            format!(
                "(ternary {} {} {})",
                TERM_PLACEHOLDER, TERM_PLACEHOLDER, TERM_PLACEHOLDER
            ),
            format!("(binary {} {})", TERM_PLACEHOLDER, TERM_PLACEHOLDER),
            format!("(unary {})", TERM_PLACEHOLDER),
        ])
        .plug("ternary", &Workload::new(&["Select"]))
        .plug(
            "binary",
            &Workload::new(&[
                "Lt", "Leq", "Eq", "Neq", "Implies", "And", "Or", "Xor", "Add", "Sub", "Mul",
                "Div", "Min", "Max",
            ]),
        )
        .plug("unary", &Workload::new(&["Not", "Neg"]))
    }

    fn atoms(&self) -> Workload {
        Workload::new(&["(Var a)", "(Var b)"])
        // Workload::new(&["(Var a)", "(Var b)", "(Lit 1)", "(Lit 0)"])
    }

    fn matches_var_pattern(&self, term: &ruler::enumo::Sexp) -> bool {
        match term {
            Sexp::List(l) => l.len() == 2 && l[0] == Sexp::Atom("Var".to_string()),
            _ => false,
        }
    }

    fn constant_pattern(&self) -> ruler::enumo::Pattern {
        "(Lit ?x)".parse().unwrap()
    }
    fn interpret_term(&mut self, term: &ruler::enumo::Sexp) -> chompy::CVec<Self> {
        if self.memo.contains_key(&term.to_string()) {
            return self.memo.get(&term.to_string()).unwrap().clone();
        }
        let res = match term {
            Sexp::Atom(a) => panic!("Unexpected atom {}", a),
            Sexp::List(l) => {
                assert!(l.len() > 1);
                let op = l[0].to_string();
                match op.as_str() {
                    "Lit" => {
                        if let Sexp::Atom(num) = &l[1] {
                            let parsed: i64 = num.parse().unwrap();
                            vec![Some(parsed); CVEC_LEN]
                        } else {
                            panic!("Term with weird structure: {}", term)
                        }
                    }
                    "Var" => self.get_env().get(&l[1].to_string()).unwrap().clone(),
                    _ => {
                        let zero: i64 = 0;
                        let one: i64 = 1;

                        let children: Vec<CVec<Self>> =
                            l[1..].iter().map(|t| self.interpret_term(t)).collect();

                        if let Sexp::Atom(op) = &l[0] {
                            match children.len() {
                                1 => {
                                    let f = |a: Option<i64>| -> Option<i64> {
                                        if a.is_none() {
                                            return None;
                                        }
                                        let a = a.unwrap();
                                        match op.as_str() {
                                            "Not" => {
                                                if a == zero {
                                                    Some(one.clone())
                                                } else {
                                                    Some(zero.clone())
                                                }
                                            }
                                            "Neg" => Some(-a),
                                            _ => panic!("Unexpected unary operator {}", op),
                                        }
                                    };

                                    children[0].iter().map(|a| f(*a)).collect()
                                }
                                2 => {
                                    let f = |(a, b): (Option<i64>, Option<i64>)| -> Option<i64> {
                                        if a.is_none() || b.is_none() {
                                            return None;
                                        }
                                        let a = a.unwrap();
                                        let b = b.unwrap();
                                        match op.as_str() {
                                            "Lt" => {
                                                Some(if a < b { one.clone() } else { zero.clone() })
                                            }
                                            "Leq" => Some(if a <= b {
                                                one.clone()
                                            } else {
                                                zero.clone()
                                            }),
                                            "Eq" => Some(if a == b {
                                                one.clone()
                                            } else {
                                                zero.clone()
                                            }),
                                            "Neq" => Some(if a != b {
                                                one.clone()
                                            } else {
                                                zero.clone()
                                            }),
                                            "Implies" => {
                                                let p = a != zero;
                                                let q = b != zero;
                                                Some(if p || !q {
                                                    one.clone()
                                                } else {
                                                    zero.clone()
                                                })
                                            }
                                            "And" => {
                                                let abool = a != zero;
                                                let bbool = b != zero;
                                                if abool && bbool {
                                                    Some(one.clone())
                                                } else {
                                                    Some(zero.clone())
                                                }
                                            }
                                            "Or" => {
                                                let abool = a != zero;
                                                let bbool = b != zero;
                                                if abool || bbool {
                                                    Some(one.clone())
                                                } else {
                                                    Some(zero.clone())
                                                }
                                            }
                                            "Xor" => {
                                                let abool = a != zero;
                                                let bbool = b != zero;
                                                if abool ^ bbool {
                                                    Some(one.clone())
                                                } else {
                                                    Some(zero.clone())
                                                }
                                            }
                                            "Add" => a.checked_add(b),
                                            "Sub" => a.checked_sub(b),
                                            "Mul" => a.checked_mul(b),
                                            "Div" => {
                                                if b.is_zero() {
                                                    Some(zero.clone())
                                                } else {
                                                    a.checked_div(b)
                                                }
                                            }
                                            "Min" => Some(a.min(b)),
                                            "Max" => Some(a.max(b)),
                                            _ => panic!("Unexpected binary operator {}", op),
                                        }
                                    };
                                    children[0]
                                        .iter()
                                        .zip(children[1].iter())
                                        .map(|(a, b)| f((*a, *b)))
                                        .into_iter()
                                        .collect()
                                }
                                3 => {
                                    let f = |(a, b, c): (Option<i64>, Option<i64>, Option<i64>)| {
                                        if a.is_none() || b.is_none() || c.is_none() {
                                            return None;
                                        }
                                        let a = a.unwrap();
                                        let b = b.unwrap();
                                        let c = c.unwrap();
                                        match op.as_str() {
                                            "Select" => Some(if a != zero { b } else { c }),
                                            _ => panic!("Unexpected ternary operator {}", op),
                                        }
                                    };
                                    children[0]
                                        .iter()
                                        .zip(children[1].iter())
                                        .zip(children[2].iter())
                                        .map(|((a, b), c)| f((*a, *b, *c)))
                                        .into_iter()
                                        .collect()
                                }
                                _ => todo!(),
                            }
                        } else {
                            panic!("Expected atom for function, found {}", op);
                        }
                    }
                }
            }
        };
        self.memo.insert(term.to_string(), res.clone());
        res
    }

    fn interpret_pred(&mut self, term: &ruler::enumo::Sexp) -> Vec<bool> {
        let cvec = self.interpret_term(term);
        cvec.iter()
            .map(|x| {
                if x.is_none() {
                    panic!(
                        "Expected concrete value for cvec {:?}, but found None",
                        cvec
                    );
                }
                let x = x.unwrap();
                if x == 0 {
                    false
                } else if x == 1 {
                    true
                } else {
                    panic!("Expected 0 or 1, but found {} in {:?}", x, cvec);
                }
            })
            .collect()
    }

    fn validate_rule(&self, rule: &chompy::Rule) -> ValidationResult {
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let lexpr = sexp_to_z3(&ctx, &rule.lhs);
        let rexpr = sexp_to_z3(&ctx, &rule.rhs);
        if rule.condition.is_some() {
            let assumption = rule.condition.clone().unwrap().0;
            let aexpr = sexp_to_z3(&ctx, &assumption);
            let zero = z3::ast::Int::from_i64(&ctx, 0);
            let cond = z3::ast::Bool::not(&aexpr._eq(&zero));
            solver.assert(&z3::ast::Bool::implies(&cond, &lexpr._eq(&rexpr)).not());
        } else {
            solver.assert(&lexpr._eq(&rexpr).not());
        }
        match solver.check() {
            z3::SatResult::Unsat => ValidationResult::Valid,
            z3::SatResult::Unknown => ValidationResult::Unknown,
            z3::SatResult::Sat => ValidationResult::Invalid,
        }
    }

    fn make_preds(&self) -> Workload {
        // TODO: expand this to have a larger range of predicates.
        let depth_1 = Workload::new(&["(Lt var var)", "(Leq var var)", "(Eq var var)"])
            .plug("var", &self.atoms());
        depth_1
    }

    fn get_env(&self) -> &ruler::HashMap<String, CVec<Self>> {
        &self.env
    }
}

impl HalideChomper {
    pub fn make_env(rng: &mut StdRng) -> HashMap<String, Vec<Option<i64>>> {
        let mut env = HashMap::default();
        let dummy = HalideChomper {
            env: env.clone(),
            memo: Default::default(),
        };
        for atom in &dummy.atoms().force() {
            if let Sexp::List(l) = atom {
                let atom_type = l[0].clone();
                if atom_type.to_string() == "Var" {
                    let id = &l[1];
                    println!("id: {:?}", id);
                    let name = id.to_string();
                    let mut values = Vec::new();
                    for _ in 0..CVEC_LEN {
                        values.push(Some(rng.gen_range(-10..10)));
                    }
                    env.insert(name, values);
                }
            }
        }
        env
    }
}

pub fn get_vars(sexp: &Sexp) -> HashSet<String> {
    let mut vars: HashSet<String> = HashSet::default();
    get_vars_internal(sexp, &mut vars);
    vars
}

fn get_vars_internal(sexp: &Sexp, vars: &mut HashSet<String>) {
    match sexp {
        Sexp::Atom(a) => {
            if a.starts_with("?") {
                // remove the "?"
                vars.insert(a[1..].to_string());
            }
        }
        Sexp::List(l) => {
            for term in l {
                get_vars_internal(term, vars);
            }
        }
    }
}

// fn get_vars(ast: z3::ast::Int) -> Vec<String> {
//     let mut vars: HashSet<String> = HashSet::default();
//     match ast {
//         z3::ast::Int::
//     }
// }

// generates a binding from variables -> values that satisfy
// the given condition.
pub fn generate_environment(cond: &Sexp) -> HashMap<String, Sexp> {
    let mut cfg = z3::Config::new();
    cfg.set_timeout_msec(1000);
    let ctx = z3::Context::new(&cfg);
    let solver = z3::Solver::new(&ctx);
    let constraint = sexp_to_z3(&ctx, cond);
    solver.assert(&constraint._eq(&z3::ast::Int::from_i64(&ctx, 1)));
    let result = solver.check();
    let mut env = HashMap::default();
    if result == z3::SatResult::Sat {
        let model = solver.get_model();
        // TODO: clean this up. this kind of string manipulation is not ideal.
        // we should be able to parse the z3 expression for
        // constants and extract the values through interpretation of the model.
        let model_str = model.unwrap().to_string();
        let lines: Vec<&str> = model_str.lines().collect();
        for line in lines {
            println!("line: {}", line);
            // split on "->"
            let parts = line.split("->").collect::<Vec<&str>>();
            if parts.len() != 2 {
                panic!("Unexpected number of parts: {}", parts.len());
            }
            // remove parens
            let var = parts[0].trim().trim_matches(|c| c == '(' || c == ')');
            let val = parts[1]
                .trim()
                .trim_matches(|c| c == '(' || c == ')')
                .replace(' ', "");
            println!("val: {}", val);
            let val_num: i64 = val.parse().unwrap();
            let sexp = Sexp::from_str(&format!("(Lit {})", val_num).to_string()).unwrap();
            // do we need CVEC_LEN here?
            env.insert(var.to_string(), sexp);
        }
    }
    env
}

fn sexp_to_z3<'a>(ctx: &'a z3::Context, sexp: &Sexp) -> z3::ast::Int<'a> {
    match sexp {
        Sexp::Atom(a) => {
            // assert that a begins with question mark
            assert!(a.starts_with("?"));
            z3::ast::Int::new_const(ctx, a[1..].to_string())
        }
        Sexp::List(l) => {
            assert!(l.len() > 1);
            let op = l[0].to_string();
            match op.as_str() {
                "Lit" => {
                    if let Sexp::Atom(num) = &l[1] {
                        let parsed: i64 = num.parse().unwrap();
                        z3::ast::Int::from_i64(ctx, parsed)
                    } else {
                        panic!("Lit with weird structure: {:?}", sexp)
                    }
                }
                _ => {
                    let children: Vec<z3::ast::Int> =
                        l[1..].iter().map(|t| sexp_to_z3(ctx, t)).collect();
                    let zero = z3::ast::Int::from_i64(ctx, 0);
                    let one = z3::ast::Int::from_i64(ctx, 1);
                    let op = l[0].to_string();
                    match op.as_str() {
                        "Lt" => z3::ast::Bool::ite(
                            &z3::ast::Int::lt(&children[0], &children[1]),
                            &one,
                            &zero,
                        ),
                        "Leq" => z3::ast::Bool::ite(
                            &z3::ast::Int::le(&children[0], &children[1]),
                            &one,
                            &zero,
                        ),
                        "Eq" => z3::ast::Bool::ite(
                            &z3::ast::Int::_eq(&children[0], &children[1]),
                            &one,
                            &zero,
                        ),
                        "Neq" => z3::ast::Bool::ite(
                            &z3::ast::Int::_eq(&children[0], &children[1]),
                            &zero,
                            &one,
                        ),
                        "Implies" => {
                            let l_not_z = z3::ast::Bool::not(&children[0]._eq(&zero));
                            let r_not_z = z3::ast::Bool::not(&children[1]._eq(&zero));
                            z3::ast::Bool::ite(
                                &z3::ast::Bool::implies(&l_not_z, &r_not_z),
                                &one,
                                &zero,
                            )
                        }
                        "Not" => z3::ast::Bool::ite(&children[0]._eq(&zero), &one, &zero),
                        "Neg" => z3::ast::Int::unary_minus(&children[0]),
                        "And" => {
                            let l_not_z = z3::ast::Bool::not(&children[0]._eq(&zero));
                            let r_not_z = z3::ast::Bool::not(&children[1]._eq(&zero));
                            z3::ast::Bool::ite(
                                &z3::ast::Bool::and(ctx, &[&l_not_z, &r_not_z]),
                                &one,
                                &zero,
                            )
                        }
                        "Or" => {
                            let l_not_z = z3::ast::Bool::not(&children[0]._eq(&zero));
                            let r_not_z = z3::ast::Bool::not(&children[1]._eq(&zero));
                            z3::ast::Bool::ite(
                                &z3::ast::Bool::or(ctx, &[&l_not_z, &r_not_z]),
                                &one,
                                &zero,
                            )
                        }
                        "Xor" => {
                            let l_not_z = z3::ast::Bool::not(&children[0]._eq(&zero));
                            let r_not_z = z3::ast::Bool::not(&children[1]._eq(&zero));
                            z3::ast::Bool::ite(&z3::ast::Bool::xor(&l_not_z, &r_not_z), &one, &zero)
                        }
                        "Add" => z3::ast::Int::add(ctx, &[&children[0], &children[1]]),
                        "Sub" => z3::ast::Int::sub(ctx, &[&children[0], &children[1]]),
                        "Mul" => z3::ast::Int::mul(ctx, &[&children[0], &children[1]]),
                        "Div" => z3::ast::Bool::ite(
                            &children[1]._eq(&zero),
                            &zero,
                            &z3::ast::Int::div(&children[0], &children[1]),
                        ),
                        "Min" => z3::ast::Bool::ite(
                            &z3::ast::Int::le(&children[0], &children[1]),
                            &children[0],
                            &children[1],
                        ),
                        "Max" => z3::ast::Bool::ite(
                            &z3::ast::Int::le(&children[0], &children[1]),
                            &children[1],
                            &children[0],
                        ),
                        "Select" => {
                            let cond = z3::ast::Bool::not(&children[0]._eq(&zero));
                            z3::ast::Bool::ite(&cond, &children[1], &children[2])
                        }
                        _ => panic!("Unexpected operator {}", op),
                    }
                }
            }
        }
    }
}

pub mod tests {
    use std::sync::Arc;

    use chompy::{init_egraph, ite::DummySort};
    use egglog::{sort::EqSort, EGraph};

    use super::*;

    // not running for now because is expensive.
    // #[test]
    fn run_halide_chomper() {
        let env = HalideChomper::make_env(&mut StdRng::seed_from_u64(0));
        let mut chomper = HalideChomper {
            env,
            memo: Default::default(),
        };
        let mut egraph = EGraph::default();

        #[derive(Debug)]
        struct HalidePredicateInterpreter {
            chomper: HalideChomper,
        }

        impl chompy::ite::PredicateInterpreter for HalidePredicateInterpreter {
            fn interp_cond(&self, sexp: &Sexp) -> bool {
                let cvec = self.chomper.clone().interpret_term(sexp);
                cvec.iter().all(|x| x.is_some() && x.unwrap() != 0)
            }
        }

        // TODO: this is only safe if we make sure the chomper doesn't actually store any state.
        let pred_interpreter = HalidePredicateInterpreter {
            chomper: chomper.clone(),
        };

        let halide_sort = Arc::new(EqSort {
            name: "HalideExpr".into(),
        });
        let dummy_sort = Arc::new(DummySort {
            sort: halide_sort.clone(),
            interpreter: Arc::new(pred_interpreter),
        });
        egraph.add_arcsort(halide_sort.clone()).unwrap();
        egraph.add_arcsort(dummy_sort).unwrap();
        init_egraph!(egraph, "../egglog/halide.egg");

        chomper.run_chompy(&mut egraph);
    }
}
