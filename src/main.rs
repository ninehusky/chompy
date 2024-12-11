// use chompy::{CVec, Chomper, Rule}; use rand::{rngs::StdRng, Rng, SeedableRng}; use ruler::{ enumo::{Sexp, Workload}, HashMap, ValidationResult, }; use chompy::init_egraph; use chompy::ite::DummySort; use egglog::{sort::EqSort, EGraph}; use std::sync::Arc; use std::io::Write;
// use z3::ast::Ast;
//
// use chompy::utils::TERM_PLACEHOLDER;
// use num::Zero;
//
// mod halide;
//
// pub const CVEC_LEN: usize = 20;
//
// #[derive(Debug, Clone)]
// pub struct HalideChomper {
//     pub env: ruler::HashMap<String, CVec<Self>>,
// }
//
// impl Chomper for HalideChomper {
//     type Constant = i64;
//     type Value = i64;
//
//     fn make_constant(&self, constant: chompy::Constant<Self>) -> Sexp {
//         Sexp::List(vec![
//             Sexp::Atom("Lit".to_string()),
//             Sexp::Atom(constant.to_string()),
//         ])
//     }
//
//     fn language_name() -> String {
//         "HalideExpr".to_string()
//     }
//
//     fn make_var(&self, var: &str) -> Sexp {
//         Sexp::List(vec![
//             Sexp::Atom("Var".to_string()),
//             Sexp::Atom(var.to_string()),
//         ])
//     }
//
//     fn get_name_from_var(&self, var: &Sexp) -> String {
//         match var {
//             Sexp::List(l) => {
//                 assert_eq!(l.len(), 2);
//                 if let Sexp::Atom(name) = &l[1] {
//                     name.clone()
//                 } else {
//                     panic!("Expected atom for variable name, found {:?}", l[1])
//                 }
//             }
//             _ => panic!("Expected list for variable, found {:?}", var),
//         }
//     }
//
//     fn productions(&self) -> ruler::enumo::Workload {
//         Workload::new(&[
//             // format!(
//             //     "(ternary {} {} {})",
//             //     TERM_PLACEHOLDER, TERM_PLACEHOLDER, TERM_PLACEHOLDER
//             // ),
//             format!("(binary {} {})", TERM_PLACEHOLDER, TERM_PLACEHOLDER),
//             format!("(unary {})", TERM_PLACEHOLDER),
//         ])
//         .plug("ternary", &Workload::new(&["Select"]))
//         .plug(
//             "binary",
//             &Workload::new(&[
//                 "Lt", "Leq", "Eq", "Neq", "Implies", "And", "Or", "Xor", "Add", "Sub", "Mul",
//                 "Div", "Min", "Max",
//             ]),
//         )
//         .plug("unary", &Workload::new(&["Not", "Neg"]))
//     }
//
//     fn atoms(&self) -> Workload {
//         // Workload::new(&["(Var a)", "(Var b)", "(Lit 1)", "(Lit 0)"])
//         Workload::new(&["(Var a)", "(Var b)"])
//     }
//
//     fn matches_var_pattern(&self, term: &ruler::enumo::Sexp) -> bool {
//         match term {
//             Sexp::List(l) => l.len() == 2 && l[0] == Sexp::Atom("Var".to_string()),
//             _ => false,
//         }
//     }
//
//     fn constant_pattern(&self) -> ruler::enumo::Pattern {
//         "(Lit ?x)".parse().unwrap()
//     }
//     fn interpret_term(&mut self, term: &ruler::enumo::Sexp) -> chompy::CVec<Self> {
//         match term {
//             Sexp::Atom(a) => panic!("Unexpected atom {}", a),
//             Sexp::List(l) => {
//                 assert!(l.len() > 1);
//                 let op = l[0].to_string();
//                 match op.as_str() {
//                     "Lit" => {
//                         if let Sexp::Atom(num) = &l[1] {
//                             let parsed: i64 = num.parse().unwrap();
//                             vec![Some(parsed); CVEC_LEN]
//                         } else {
//                             panic!("Term with weird structure: {}", term)
//                         }
//                     }
//                     "Var" => {
//                         let result = self.get_env().get(&l[1].to_string());
//                         if result.is_none() {
//                             panic!("For term {:?}, could not find variable {:?}", term, l[1]);
//                         }
//                         result.unwrap().clone()
//                     }
//                     _ => {
//                         let zero: i64 = 0;
//                         let one: i64 = 1;
//
//                         let children: Vec<CVec<Self>> =
//                             l[1..].iter().map(|t| self.interpret_term(t)).collect();
//
//                         if let Sexp::Atom(op) = &l[0] {
//                             match children.len() {
//                                 1 => {
//                                     let f = |a: Option<i64>| -> Option<i64> {
//                                         if a.is_none() {
//                                             return None;
//                                         }
//                                         let a = a.unwrap();
//                                         match op.as_str() {
//                                             "Not" => {
//                                                 if a == zero {
//                                                     Some(one.clone())
//                                                 } else {
//                                                     Some(zero.clone())
//                                                 }
//                                             }
//                                             "Neg" => Some(-a),
//                                             _ => panic!("Unexpected unary operator {}", op),
//                                         }
//                                     };
//
//                                     children[0].iter().map(|a| f(*a)).collect()
//                                 }
//                                 2 => {
//                                     let f = |(a, b): (Option<i64>, Option<i64>)| -> Option<i64> {
//                                         if a.is_none() || b.is_none() {
//                                             return None;
//                                         }
//                                         let a = a.unwrap();
//                                         let b = b.unwrap();
//                                         match op.as_str() {
//                                             "Lt" => {
//                                                 Some(if a < b { one.clone() } else { zero.clone() })
//                                             }
//                                             "Leq" => Some(if a <= b {
//                                                 one.clone()
//                                             } else {
//                                                 zero.clone()
//                                             }),
//                                             "Eq" => Some(if a == b {
//                                                 one.clone()
//                                             } else {
//                                                 zero.clone()
//                                             }),
//                                             "Neq" => Some(if a != b {
//                                                 one.clone()
//                                             } else {
//                                                 zero.clone()
//                                             }),
//                                             "Implies" => {
//                                                 let p = a != zero;
//                                                 let q = b != zero;
//                                                 Some(if p || !q {
//                                                     one.clone()
//                                                 } else {
//                                                     zero.clone()
//                                                 })
//                                             }
//                                             "And" => {
//                                                 let abool = a != zero;
//                                                 let bbool = b != zero;
//                                                 if abool && bbool {
//                                                     Some(one.clone())
//                                                 } else {
//                                                     Some(zero.clone())
//                                                 }
//                                             }
//                                             "Or" => {
//                                                 let abool = a != zero;
//                                                 let bbool = b != zero;
//                                                 if abool || bbool {
//                                                     Some(one.clone())
//                                                 } else {
//                                                     Some(zero.clone())
//                                                 }
//                                             }
//                                             "Xor" => {
//                                                 let abool = a != zero;
//                                                 let bbool = b != zero;
//                                                 if abool ^ bbool {
//                                                     Some(one.clone())
//                                                 } else {
//                                                     Some(zero.clone())
//                                                 }
//                                             }
//                                             "Add" => a.checked_add(b),
//                                             "Sub" => a.checked_sub(b),
//                                             "Mul" => a.checked_mul(b),
//                                             "Div" => {
//                                                 if b.is_zero() {
//                                                     Some(zero.clone())
//                                                 } else {
//                                                     a.checked_div(b)
//                                                 }
//                                             }
//                                             "Min" => Some(a.min(b)),
//                                             "Max" => Some(a.max(b)),
//                                             _ => panic!("Unexpected binary operator {}", op),
//                                         }
//                                     };
//                                     children[0]
//                                         .iter()
//                                         .zip(children[1].iter())
//                                         .map(|(a, b)| f((*a, *b)))
//                                         .into_iter()
//                                         .collect()
//                                 }
//                                 3 => {
//                                     let f = |(a, b, c): (Option<i64>, Option<i64>, Option<i64>)| {
//                                         if a.is_none() || b.is_none() || c.is_none() {
//                                             return None;
//                                         }
//                                         let a = a.unwrap();
//                                         let b = b.unwrap();
//                                         let c = c.unwrap();
//                                         match op.as_str() {
//                                             "Select" => Some(if a != zero { b } else { c }),
//                                             _ => panic!("Unexpected ternary operator {}", op),
//                                         }
//                                     };
//                                     children[0]
//                                         .iter()
//                                         .zip(children[1].iter())
//                                         .zip(children[2].iter())
//                                         .map(|((a, b), c)| f((*a, *b, *c)))
//                                         .into_iter()
//                                         .collect()
//                                 }
//                                 _ => todo!(),
//                             }
//                         } else {
//                             panic!("Expected atom for function, found {}", op);
//                         }
//                     }
//                 }
//             }
//         }
//     }
//
//     fn interpret_pred(&self, term: &ruler::enumo::Sexp) -> Vec<bool> {
//         let cvec = self.interpret_term(term);
//         cvec.iter()
//             .map(|x| {
//                 if x.is_none() {
//                     panic!(
//                         "Expected concrete value for cvec {:?}, but found None",
//                         cvec
//                     );
//                 }
//                 let x = x.unwrap();
//                 if x == 0 {
//                     false
//                 } else if x == 1 {
//                     true
//                 } else {
//                     panic!("Expected 0 or 1, but found {} in {:?}", x, cvec);
//                 }
//             })
//             .collect()
//     }
//
//     fn validate_rule(&self, rule: &chompy::Rule) -> ValidationResult {
//         let mut cfg = z3::Config::new();
//         cfg.set_timeout_msec(1000);
//         let ctx = z3::Context::new(&cfg);
//         let solver = z3::Solver::new(&ctx);
//         let lexpr = sexp_to_z3(&ctx, &rule.lhs);
//         let rexpr = sexp_to_z3(&ctx, &rule.rhs);
//         if rule.condition.is_some() {
//             let assumption = rule.condition.clone().unwrap().0;
//             let aexpr = sexp_to_z3(&ctx, &assumption);
//             let zero = z3::ast::Int::from_i64(&ctx, 0);
//             let cond = z3::ast::Bool::not(&aexpr._eq(&zero));
//             solver.assert(&z3::ast::Bool::implies(&cond, &lexpr._eq(&rexpr)).not());
//         } else {
//             solver.assert(&lexpr._eq(&rexpr).not());
//         }
//         match solver.check() {
//             z3::SatResult::Unsat => ValidationResult::Valid,
//             z3::SatResult::Unknown => ValidationResult::Unknown,
//             z3::SatResult::Sat => ValidationResult::Invalid,
//         }
//     }
//
//     fn make_preds(&self) -> Workload {
//         // TODO: expand this to have a larger range of predicates.
//         let depth_1 = Workload::new(&["(Lt var var)", "(Leq var var)", "(Eq var var)"])
//             .plug("var", &self.atoms());
//         depth_1
//     }
//
//     fn get_env(&self) -> &ruler::HashMap<String, CVec<Self>> {
//         &self.env
//     }
// }
//
// impl HalideChomper {
//     fn make_env(rng: &mut StdRng) -> HashMap<String, Vec<Option<i64>>> {
//         let mut env = HashMap::default();
//         let dummy = HalideChomper { env: env.clone() };
//         for atom in &dummy.atoms().force() {
//             if let Sexp::List(l) = atom {
//                 let atom_type = l[0].clone();
//                 if atom_type.to_string() == "Var" {
//                     let id = &l[1];
//                     println!("id: {:?}", id);
//                     let name = id.to_string();
//                     let mut values = Vec::new();
//                     for _ in 0..CVEC_LEN {
//                         values.push(Some(rng.gen_range(-10..10)));
//                     }
//                     env.insert(name, values);
//                 }
//             }
//         }
//         env
//     }
// }
//
// fn sexp_to_z3<'a>(ctx: &'a z3::Context, sexp: &Sexp) -> z3::ast::Int<'a> {
//     match sexp {
//         Sexp::Atom(a) => {
//             // assert that a begins with question mark
//             assert!(a.starts_with("?"));
//             z3::ast::Int::new_const(ctx, a[1..].to_string())
//         }
//         Sexp::List(l) => {
//             assert!(l.len() > 1);
//             let op = l[0].to_string();
//             match op.as_str() {
//                 "Lit" => {
//                     if let Sexp::Atom(num) = &l[1] {
//                         let parsed: i64 = num.parse().unwrap();
//                         z3::ast::Int::from_i64(ctx, parsed)
//                     } else {
//                         panic!("Lit with weird structure: {:?}", sexp)
//                     }
//                 }
//                 _ => {
//                     let children: Vec<z3::ast::Int> =
//                         l[1..].iter().map(|t| sexp_to_z3(ctx, t)).collect();
//                     let zero = z3::ast::Int::from_i64(ctx, 0);
//                     let one = z3::ast::Int::from_i64(ctx, 1);
//                     let op = l[0].to_string();
//                     match op.as_str() {
//                         "Lt" => z3::ast::Bool::ite(
//                             &z3::ast::Int::lt(&children[0], &children[1]),
//                             &one,
//                             &zero,
//                         ),
//                         "Leq" => z3::ast::Bool::ite(
//                             &z3::ast::Int::le(&children[0], &children[1]),
//                             &one,
//                             &zero,
//                         ),
//                         "Eq" => z3::ast::Bool::ite(
//                             &z3::ast::Int::_eq(&children[0], &children[1]),
//                             &one,
//                             &zero,
//                         ),
//                         "Neq" => z3::ast::Bool::ite(
//                             &z3::ast::Int::_eq(&children[0], &children[1]),
//                             &zero,
//                             &one,
//                         ),
//                         "Implies" => {
//                             let l_not_z = z3::ast::Bool::not(&children[0]._eq(&zero));
//                             let r_not_z = z3::ast::Bool::not(&children[1]._eq(&zero));
//                             z3::ast::Bool::ite(
//                                 &z3::ast::Bool::implies(&l_not_z, &r_not_z),
//                                 &one,
//                                 &zero,
//                             )
//                         }
//                         "Not" => z3::ast::Bool::ite(&children[0]._eq(&zero), &one, &zero),
//                         "Neg" => z3::ast::Int::unary_minus(&children[0]),
//                         "And" => {
//                             let l_not_z = z3::ast::Bool::not(&children[0]._eq(&zero));
//                             let r_not_z = z3::ast::Bool::not(&children[1]._eq(&zero));
//                             z3::ast::Bool::ite(
//                                 &z3::ast::Bool::and(ctx, &[&l_not_z, &r_not_z]),
//                                 &one,
//                                 &zero,
//                             )
//                         }
//                         "Or" => {
//                             let l_not_z = z3::ast::Bool::not(&children[0]._eq(&zero));
//                             let r_not_z = z3::ast::Bool::not(&children[1]._eq(&zero));
//                             z3::ast::Bool::ite(
//                                 &z3::ast::Bool::or(ctx, &[&l_not_z, &r_not_z]),
//                                 &one,
//                                 &zero,
//                             )
//                         }
//                         "Xor" => {
//                             let l_not_z = z3::ast::Bool::not(&children[0]._eq(&zero));
//                             let r_not_z = z3::ast::Bool::not(&children[1]._eq(&zero));
//                             z3::ast::Bool::ite(&z3::ast::Bool::xor(&l_not_z, &r_not_z), &one, &zero)
//                         }
//                         "Add" => z3::ast::Int::add(ctx, &[&children[0], &children[1]]),
//                         "Sub" => z3::ast::Int::sub(ctx, &[&children[0], &children[1]]),
//                         "Mul" => z3::ast::Int::mul(ctx, &[&children[0], &children[1]]),
//                         "Div" => z3::ast::Bool::ite(
//                             &children[1]._eq(&zero),
//                             &zero,
//                             &z3::ast::Int::div(&children[0], &children[1]),
//                         ),
//                         "Min" => z3::ast::Bool::ite(
//                             &z3::ast::Int::le(&children[0], &children[1]),
//                             &children[0],
//                             &children[1],
//                         ),
//                         "Max" => z3::ast::Bool::ite(
//                             &z3::ast::Int::le(&children[0], &children[1]),
//                             &children[1],
//                             &children[0],
//                         ),
//                         "Select" => {
//                             let cond = z3::ast::Bool::not(&children[0]._eq(&zero));
//                             z3::ast::Bool::ite(&cond, &children[1], &children[2])
//                         }
//                         _ => panic!("Unexpected operator {}", op),
//                     }
//                 }
//             }
//         }
//     }
// }
//
// fn main() {
//     env_logger::init();
//     let env = HalideChomper::make_env(&mut StdRng::seed_from_u64(0));
//     let mut chomper = HalideChomper { env };
//     let mut egraph = EGraph::default();
//
//     #[derive(Debug)]
//     struct HalidePredicateInterpreter {
//         chomper: HalideChomper,
//     }
//
//     impl chompy::ite::PredicateInterpreter for HalidePredicateInterpreter {
//         fn interp_cond(&self, sexp: &Sexp) -> bool {
//             let cvec = self.chomper.clone().interpret_term(sexp);
//             cvec.iter().all(|x| x.is_some() && x.unwrap() != 0)
//         }
//     }
//
//     // TODO: this is only safe if we make sure the chomper doesn't actually store any state.
//     let pred_interpreter = HalidePredicateInterpreter {
//         chomper: chomper.clone(),
//     };
//
//     let halide_sort = Arc::new(EqSort {
//         name: "HalideExpr".into(),
//     });
//     let dummy_sort = Arc::new(DummySort {
//         sort: halide_sort.clone(),
//         interpreter: Arc::new(pred_interpreter),
//     });
//     egraph.add_arcsort(halide_sort.clone()).unwrap();
//     egraph.add_arcsort(dummy_sort).unwrap();
//     init_egraph!(egraph, "../tests/egglog/halide.egg");
//
//     let initial_egraph = egraph.clone();
//
//     let start_time = std::time::Instant::now();
//     let rules = chomper.run_chompy(&mut egraph);
//     let elapsed = start_time.elapsed();
//
//     // output each rule to synth-rules.txt
//     let mut file = std::fs::File::create("synth-rules.txt").unwrap();
//     file.write_all(
//         format!(
//             "{} rules found in {} seconds\n\n",
//             rules.len(),
//             elapsed.as_secs_f64()
//         )
//         .as_bytes(),
//     )
//     .unwrap();
//     for rule in &rules {
//         match &rule.condition {
//             Some((cond, _)) => {
//                 file.write_all(
//                     format!("if {} then {} ~> {}\n\n", cond, rule.lhs, rule.rhs).as_bytes(),
//                 )
//                 .unwrap();
//             }
//             None => {
//                 file.write_all(format!("{} ~> {}\n\n", rule.lhs, rule.rhs).as_bytes())
//                     .unwrap();
//             }
//         }
//     }
//
//     let handwritten_rules = halide::get_validated_handwritten_rules();
//
//     let mut rng = StdRng::seed_from_u64(0);
//
//     // for each handwritten rule, see if it is derivable from the rules found by chompy.
//     let mut found_rules_count = 0;
//     let total_rules = handwritten_rules.len();
//     for rule in handwritten_rules {
//         let generalized = chomper.generalize_rule(&rule);
//         let env = {
//             if let Some((cond, _)) = &generalized.condition {
//                 halide::halide::generate_environment(&cond)
//             } else {
//                 HashMap::default()
//             }
//         };
//         // halide::generate_environment(&(generalized.condition.clone().unwrap().0));
//         // put random values in for non-conditioned variables.
//         // union the variables in the lhs and rhs.
//         let lhs_vars = halide::halide::get_vars(&generalized.lhs);
//         let rhs_vars = halide::halide::get_vars(&generalized.rhs);
//
//         let mut higher_lvl_env: HashMap<String, Vec<Option<i64>>> = HashMap::default();
//
//         for var in lhs_vars.union(&rhs_vars) {
//             if !higher_lvl_env.contains_key(var) {
//                 let num: i64 = rng.gen();
//                 let num = num % 10;
//                 higher_lvl_env.insert(var.clone(), vec![Some(num)]);
//             }
//         }
//
//         let mut chomper = HalideChomper {
//             env: higher_lvl_env.clone(),
//         };
//
//         println!("higher_lvl_env: {:?}", higher_lvl_env);
//
//         let cond = if let Some((cond, _)) = &generalized.condition {
//             Some((cond.clone(), vec![env]))
//         } else {
//             None
//         };
//
//         // give the derivability check a timeout of 10 seconds.
//         //
//         let timeout = std::time::Duration::from_secs(10);
//
//         if chomper.check_derivability(
//             &initial_egraph.clone(),
//             &rules,
//             &Rule {
//                 condition: cond,
//                 lhs: generalized.lhs.clone(),
//                 rhs: generalized.rhs.clone(),
//             },
//             true,
//         ) {
//             found_rules_count += 1;
//         } else {
//         }
//     }
//
//     println!("Found {}/{} rules", found_rules_count, total_rules);
// }
fn main() {}
