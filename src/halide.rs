use crate::*;

use egg::{RecExpr, Rewrite};
use enumo::{Filter, Metric, Ruleset, Sexp, Workload};
use num::ToPrimitive;
use recipe_utils::{
    base_lang, iter_metric, recursive_rules, recursive_rules_cond, run_workload, Lang,
};
use z3::ast::Ast;

type Constant = i64;

egg::define_language! {
  pub enum Pred {
    Lit(Constant),
    "abs" = Abs(Id),
    "<" = Lt([Id;2]),
    "<=" = Leq([Id;2]),
    ">" = Gt([Id;2]),
    ">=" = Geq([Id;2]),
    "==" = Eq([Id;2]),
    "!=" = Neq([Id;2]),
    "->" = Implies([Id; 2]),
    "!" = Not(Id),
    "-" = Neg(Id),
    "&&" = And([Id;2]),
    "||" = Or([Id;2]),
    "^" = Xor([Id;2]),
    "+" = Add([Id; 2]),
    "-" = Sub([Id; 2]),
    "*" = Mul([Id; 2]),
    "/" = Div([Id; 2]),
    "%" = Mod([Id; 2]),
    "min" = Min([Id; 2]),
    "max" = Max([Id; 2]),
    "select" = Select([Id; 3]),
    "istrue" = IsTrue(Id),
    Var(Symbol),
  }
}

impl SynthLanguage for Pred {
    type Constant = Constant;

    fn constant_to_bool(c: &Self::Constant) -> Option<bool> {
        Some(c != &0)
    }

    fn eval<'a, F>(&'a self, cvec_len: usize, mut get_cvec: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>,
    {
        let one = 1.to_i64().unwrap();
        let zero = 0.to_i64().unwrap();
        match self {
            Pred::Lit(c) => vec![Some(*c); cvec_len],
            Pred::Abs(x) => map!(get_cvec, x => Some(x.abs())),
            Pred::Lt([x, y]) => {
                map!(get_cvec, x, y => if x < y {Some(one)} else {Some(zero)})
            }
            Pred::Leq([x, y]) => {
                map!(get_cvec, x, y => if x <= y {Some(one)} else {Some(zero)})
            }
            Pred::Gt([x, y]) => {
                map!(get_cvec, x, y => if x > y {Some(one)} else {Some(zero)})
            }
            Pred::Geq([x, y]) => {
                map!(get_cvec, x, y => if x >= y {Some(one)} else {Some(zero)})
            }
            Pred::Eq([x, y]) => {
                map!(get_cvec, x, y => if x == y {Some(one)} else {Some(zero)})
            }
            Pred::Neq([x, y]) => {
                map!(get_cvec, x, y => if x != y {Some(one)} else {Some(zero)})
            }
            Pred::Implies([x, y]) => {
                map!(get_cvec, x, y => {
                  let xbool = *x != zero;
                  let ybool = *y != zero;
                  if !xbool || ybool {Some(one)} else {Some(zero)}
                })
            }
            Pred::Not(x) => {
                map!(get_cvec, x => if *x == zero { Some(one)} else {Some(zero)})
            }
            Pred::Neg(x) => map!(get_cvec, x => Some(-x)),
            Pred::And([x, y]) => {
                map!(get_cvec, x, y => {
                    let xbool = *x != zero;
                    let ybool = *y != zero;
                    if xbool && ybool { Some(one) } else { Some(zero) }
                })
            }
            Pred::Or([x, y]) => {
                map!(get_cvec, x, y => {
                    let xbool = *x != zero;
                    let ybool = *y != zero;
                    if xbool || ybool { Some(one) } else { Some(zero) }
                })
            }
            Pred::Xor([x, y]) => {
                map!(get_cvec, x, y => {
                    let xbool = *x != zero;
                    let ybool = *y != zero;
                    if xbool ^ ybool { Some(one) } else { Some(zero) }
                })
            }
            Pred::Add([x, y]) => map!(get_cvec, x, y => x.checked_add(*y)),
            Pred::Sub([x, y]) => map!(get_cvec, x, y => x.checked_sub(*y)),
            Pred::Mul([x, y]) => map!(get_cvec, x, y => x.checked_mul(*y)),
            Pred::Div([x, y]) => map!(get_cvec, x, y => {
                if *y == zero {
                    Some(zero)
                } else {
                    let is_neg = (*x < zero) ^ (*y < zero);
                    if is_neg {
                        x.abs().checked_div(y.abs()).map(|v| -v)
                    } else {
                        x.checked_div(*y)
                    }
                }
            }),
            Pred::Mod([x, y]) => map!(get_cvec, x, y => {
                if *y == zero {
                    Some(zero)
                } else {
                    let is_neg = (*x < zero) ^ (*y < zero);
                    if is_neg {
                        x.abs().checked_rem(y.abs()).map(|v| -v)
                    } else {
                        x.checked_rem(*y)
                    }
                }
            }),
            Pred::Min([x, y]) => map!(get_cvec, x, y => Some(*x.min(y))),
            Pred::Max([x, y]) => map!(get_cvec, x, y => Some(*x.max(y))),
            Pred::Select([x, y, z]) => map!(get_cvec, x, y, z => {
              let xbool = *x != zero;
              if xbool {Some(*y)} else {Some(*z)}
            }),
            Pred::Var(_) => vec![],
            Pred::IsTrue(_) => {
                // TODO: @ninehusky - I actually kind of want to panic here, because
                // cvec matching on `istrue` is just a bad thing waiting to happen.
                // I'm actually not sure what a more principled fix would be, however,
                // so leaving it as is for now. Maybe we can kick the can to later --
                // if a rule is generated with `istrue`, we can panic then?
                vec![None, None, None]
            }
        }
    }

    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]) {
        println!("vars: {:?}", vars);
        let consts = vec![
            Some((-10).to_i64().unwrap()),
            Some((-1).to_i64().unwrap()),
            Some(0.to_i64().unwrap()),
            Some(1.to_i64().unwrap()),
            Some(2.to_i64().unwrap()),
            Some(5.to_i64().unwrap()),
            Some(100.to_i64().unwrap()),
        ];

        let cvecs = self_product(&consts, vars.len());

        egraph.analysis.cvec_len = cvecs[0].len();

        for (i, v) in vars.iter().enumerate() {
            let id = egraph.add(Pred::Var(Symbol::from(v.clone())));
            let cvec = cvecs[i].clone();
            egraph[id].data.cvec = cvec;
        }
    }

    fn to_var(&self) -> Option<Symbol> {
        if let Pred::Var(sym) = self {
            Some(*sym)
        } else {
            None
        }
    }

    fn mk_var(sym: Symbol) -> Self {
        Pred::Var(sym)
    }

    fn is_constant(&self) -> bool {
        matches!(self, Pred::Lit(_))
    }

    fn mk_constant(c: Self::Constant, _egraph: &mut EGraph<Self, SynthAnalysis>) -> Self {
        Pred::Lit(c)
    }

    fn condition_implies(
        lhs: &Pattern<Self>,
        rhs: &Pattern<Self>,
        cache: &mut HashMap<(String, String), bool>,
    ) -> bool {
        let lhs_str = lhs.to_string();
        let rhs_str = rhs.to_string();
        if cache.contains_key(&(lhs_str.clone(), rhs_str.clone())) {
            return *cache.get(&(lhs_str, rhs_str)).unwrap();
        }

        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let zero = z3::ast::Int::from_i64(&ctx, 0);

        // given that the lhs is true, can we make the rhs false?

        let lhs = egg_to_z3(&ctx, Self::instantiate(lhs).as_ref())
            ._eq(&zero)
            .not();

        let rhs = egg_to_z3(&ctx, Self::instantiate(rhs).as_ref())
            ._eq(&zero)
            .not();

        let assertion = &lhs;

        solver.assert(assertion);

        if matches!(solver.check(), z3::SatResult::Unsat) {
            // don't want something that is always false
            cache.insert((lhs_str, rhs_str), false);
            return false;
        }

        solver.reset();
        let assertion = &rhs;

        solver.assert(&assertion.not());

        if matches!(solver.check(), z3::SatResult::Unsat) {
            // don't want something that is always true
            cache.insert((lhs_str, rhs_str), false);
            return false;
        }

        solver.reset();

        let assertion = &z3::ast::Bool::implies(&lhs, &rhs).not();

        solver.assert(assertion);

        let res = solver.check();
        let implies = matches!(res, z3::SatResult::Unsat);
        cache.insert((lhs_str, rhs_str), implies);
        implies
    }

    fn validate(lhs: &Pattern<Self>, rhs: &Pattern<Self>) -> ValidationResult {
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let lexpr = egg_to_z3(&ctx, Self::instantiate(lhs).as_ref());
        let rexpr = egg_to_z3(&ctx, Self::instantiate(rhs).as_ref());
        solver.assert(&lexpr._eq(&rexpr).not());
        // if matches!(solver.check(), z3::SatResult::Sat) {
        //     let model = solver.get_model().unwrap();
        //     println!(
        //         "Rule {} ==> {} is invalid.\nthe model is:\n{:?}eval({}) = {:?}\neval({}) = {:?}\n",
        //         lhs,
        //         rhs,
        //         model,
        //         lhs,
        //         model.eval(&lexpr),
        //         rhs,
        //         model.eval(&rexpr)
        //     );
        // }
        match solver.check() {
            z3::SatResult::Unsat => ValidationResult::Valid,
            z3::SatResult::Unknown => ValidationResult::Unknown,
            z3::SatResult::Sat => ValidationResult::Invalid,
        }
    }

    fn validate_with_cond(
        lhs: &Pattern<Self>,
        rhs: &Pattern<Self>,
        cond: &Pattern<Self>,
    ) -> ValidationResult {
        assert!(cond.to_string().len() > 2, "Conditional pattern: {}", cond);
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let zero = z3::ast::Int::from_i64(&ctx, 0);
        let cexpr =
            z3::ast::Bool::not(&egg_to_z3(&ctx, Self::instantiate(cond).as_ref())._eq(&zero));

        let lexpr = egg_to_z3(&ctx, Self::instantiate(lhs).as_ref());
        let rexpr = egg_to_z3(&ctx, Self::instantiate(rhs).as_ref());
        solver.assert(&z3::ast::Bool::implies(&cexpr, &lexpr._eq(&rexpr)).not());

        // if matches!(solver.check(), z3::SatResult::Sat) {
        //     let model = solver.get_model().unwrap();
        //     println!(
        //         "Rule if {} then {} ==> {} is invalid.\nthe model is:\n{:?}eval({}) = {:?}\neval({}) = {:?}\n",
        //         cond,
        //         lhs,
        //         rhs,
        //         model,
        //         lhs,
        //         model.eval(&lexpr),
        //         rhs,
        //         model.eval(&rexpr)
        //     );
        // }

        match solver.check() {
            z3::SatResult::Unsat => ValidationResult::Valid,
            z3::SatResult::Unknown => ValidationResult::Unknown,
            z3::SatResult::Sat => ValidationResult::Invalid,
        }
    }
}

pub fn egg_to_z3<'a>(ctx: &'a z3::Context, expr: &[Pred]) -> z3::ast::Int<'a> {
    let mut buf: Vec<z3::ast::Int> = vec![];
    let zero = z3::ast::Int::from_i64(ctx, 0);
    let one = z3::ast::Int::from_i64(ctx, 1);
    for node in expr.as_ref().iter() {
        match node {
            Pred::Lit(c) => buf.push(z3::ast::Int::from_i64(ctx, c.to_i64().unwrap())),
            Pred::Abs(x) => {
                let l = &buf[usize::from(*x)];
                buf.push(z3::ast::Bool::ite(
                    &z3::ast::Int::lt(l, &zero),
                    &z3::ast::Int::unary_minus(l),
                    l,
                ))
            }
            Pred::Lt([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                buf.push(z3::ast::Bool::ite(&z3::ast::Int::lt(l, r), &one, &zero))
            }
            Pred::Leq([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                buf.push(z3::ast::Bool::ite(&z3::ast::Int::le(l, r), &one, &zero))
            }
            Pred::Gt([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                buf.push(z3::ast::Bool::ite(&z3::ast::Int::gt(l, r), &one, &zero))
            }
            Pred::Geq([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                buf.push(z3::ast::Bool::ite(&z3::ast::Int::ge(l, r), &one, &zero))
            }
            Pred::Eq([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                buf.push(z3::ast::Bool::ite(&z3::ast::Int::_eq(l, r), &one, &zero))
            }
            Pred::Neq([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                buf.push(z3::ast::Bool::ite(&z3::ast::Int::_eq(l, r), &zero, &one))
            }
            Pred::Implies([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                let l_not_z = z3::ast::Bool::not(&l._eq(&zero));
                let r_not_z = z3::ast::Bool::not(&r._eq(&zero));
                buf.push(z3::ast::Bool::ite(
                    &z3::ast::Bool::implies(&l_not_z, &r_not_z),
                    &one,
                    &zero,
                ))
            }
            Pred::Not(x) => {
                let l = &buf[usize::from(*x)];
                buf.push(z3::ast::Bool::ite(&l._eq(&zero), &one, &zero))
            }
            Pred::Neg(x) => buf.push(z3::ast::Int::unary_minus(&buf[usize::from(*x)])),
            Pred::And([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                let l_not_z = z3::ast::Bool::not(&l._eq(&zero));
                let r_not_z = z3::ast::Bool::not(&r._eq(&zero));
                buf.push(z3::ast::Bool::ite(
                    &z3::ast::Bool::and(ctx, &[&l_not_z, &r_not_z]),
                    &one,
                    &zero,
                ))
            }
            Pred::Or([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                let l_not_z = z3::ast::Bool::not(&l._eq(&zero));
                let r_not_z = z3::ast::Bool::not(&r._eq(&zero));
                buf.push(z3::ast::Bool::ite(
                    &z3::ast::Bool::or(ctx, &[&l_not_z, &r_not_z]),
                    &one,
                    &zero,
                ))
            }
            Pred::Xor([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                let l_not_z = z3::ast::Bool::not(&l._eq(&zero));
                let r_not_z = z3::ast::Bool::not(&r._eq(&zero));
                buf.push(z3::ast::Bool::ite(
                    &z3::ast::Bool::xor(&l_not_z, &r_not_z),
                    &one,
                    &zero,
                ))
            }
            Pred::Add([x, y]) => buf.push(z3::ast::Int::add(
                ctx,
                &[&buf[usize::from(*x)], &buf[usize::from(*y)]],
            )),
            Pred::Sub([x, y]) => buf.push(z3::ast::Int::sub(
                ctx,
                &[&buf[usize::from(*x)], &buf[usize::from(*y)]],
            )),
            Pred::Mul([x, y]) => buf.push(z3::ast::Int::mul(
                ctx,
                &[&buf[usize::from(*x)], &buf[usize::from(*y)]],
            )),
            Pred::Div([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];

                let zero = z3::ast::Int::from_i64(ctx, 0);

                let l_neg = z3::ast::Int::lt(l, &zero);
                let r_neg = z3::ast::Int::lt(r, &zero);

                let l_abs = z3::ast::Bool::ite(&l_neg, &z3::ast::Int::unary_minus(l), l);
                let r_abs = z3::ast::Bool::ite(&r_neg, &z3::ast::Int::unary_minus(r), r);
                let div = z3::ast::Int::div(&l_abs, &r_abs);

                let signs_differ = z3::ast::Bool::xor(&l_neg, &r_neg);

                buf.push(z3::ast::Bool::ite(
                    &r._eq(&zero),
                    &zero,
                    &z3::ast::Bool::ite(&signs_differ, &z3::ast::Int::unary_minus(&div), &div),
                ));
            }
            Pred::Mod([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];

                let zero = z3::ast::Int::from_i64(ctx, 0);

                let l_neg = z3::ast::Int::lt(l, &zero);
                let r_neg = z3::ast::Int::lt(r, &zero);

                let l_abs = z3::ast::Bool::ite(&l_neg, &z3::ast::Int::unary_minus(l), l);
                let r_abs = z3::ast::Bool::ite(&r_neg, &z3::ast::Int::unary_minus(r), r);
                let modulo = z3::ast::Int::modulo(&l_abs, &r_abs);

                let signs_differ = z3::ast::Bool::xor(&l_neg, &r_neg);

                buf.push(z3::ast::Bool::ite(
                    &r._eq(&zero),
                    &zero,
                    &z3::ast::Bool::ite(
                        &signs_differ,
                        &z3::ast::Int::unary_minus(&modulo),
                        &modulo,
                    ),
                ));
            }
            Pred::Min([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                buf.push(z3::ast::Bool::ite(&z3::ast::Int::le(l, r), l, r))
            }
            Pred::Max([x, y]) => {
                let l = &buf[usize::from(*x)];
                let r = &buf[usize::from(*y)];
                buf.push(z3::ast::Bool::ite(&z3::ast::Int::le(l, r), r, l))
            }
            Pred::Select([x, y, z]) => {
                let cond = z3::ast::Bool::not(&buf[usize::from(*x)]._eq(&zero));
                buf.push(z3::ast::Bool::ite(
                    &cond,
                    &buf[usize::from(*y)],
                    &buf[usize::from(*z)],
                ))
            }
            Pred::Var(v) => buf.push(z3::ast::Int::new_const(ctx, v.to_string())),
            Pred::IsTrue(_) => {
                panic!("IsTrue should not be used in egg_to_z3");
            }
        }
    }
    buf.pop().unwrap()
}

// This function returns if the given expression is valid or not, where validity is defined as:
// Valid   ==> The expression is always true (evaluates to 1), no matter the values of the variables inside.
// Invalid ==> The expression is always false (evaluates to 0), no matter the values of the
// variables inside.
// Unknown ==> Either the solver timed out, or the expression is impossible to condense to one of the two above.
//             One such expression is `x < 0`, which is neither always true nor always false.
//             In Caviar, this corresponds to the "Impossible" stop result.
// This function is different from `Self::validate` in that `validate` only checks to see if a
// given statement is true, while this function checks if the statement is always true or always
// false (forall).
pub fn validate_expression(expr: &Sexp) -> ValidationResult {
    pub fn sexpr_to_z3<'a>(ctx: &'a z3::Context, expr: &Sexp) -> z3::ast::Int<'a> {
        match expr {
            Sexp::Atom(a) => {
                if let Ok(c) = a.parse::<i64>() {
                    z3::ast::Int::from_i64(ctx, c)
                } else {
                    z3::ast::Int::new_const(ctx, a.to_string())
                }
            }
            Sexp::List(l) => {
                let mut iter = l.iter();
                let head = iter.next().unwrap();
                let tail = iter.collect::<Vec<_>>();
                match head.to_string().as_str() {
                    "abs" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        z3::ast::Bool::ite(
                            &z3::ast::Int::lt(&x, &z3::ast::Int::from_i64(ctx, 0)),
                            &z3::ast::Int::unary_minus(&x),
                            &x,
                        )
                    }
                    "<" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Bool::ite(
                            &z3::ast::Int::lt(&x, &y),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    "<=" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Bool::ite(
                            &z3::ast::Int::le(&x, &y),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    ">" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Bool::ite(
                            &z3::ast::Int::gt(&x, &y),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    ">=" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Bool::ite(
                            &z3::ast::Int::ge(&x, &y),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    "==" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Bool::ite(
                            &z3::ast::Int::_eq(&x, &y),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    "!=" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Bool::ite(
                            &z3::ast::Int::_eq(&x, &y),
                            &z3::ast::Int::from_i64(ctx, 0),
                            &z3::ast::Int::from_i64(ctx, 1),
                        )
                    }
                    "->" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        let x_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &x,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        let y_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &y,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        z3::ast::Bool::ite(
                            &z3::ast::Bool::implies(&x_not_z, &y_not_z),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    "!" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        z3::ast::Bool::ite(
                            &z3::ast::Int::_eq(&x, &z3::ast::Int::from_i64(ctx, 0)),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    "-" => {
                        if tail.len() == 1 {
                            z3::ast::Int::unary_minus(&sexpr_to_z3(ctx, tail[0]))
                        } else {
                            let x = sexpr_to_z3(ctx, tail[0]);
                            let y = sexpr_to_z3(ctx, tail[1]);
                            z3::ast::Int::sub(ctx, &[&x, &y])
                        }
                    }
                    "&&" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        let x_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &x,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        let y_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &y,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        z3::ast::Bool::ite(
                            &z3::ast::Bool::and(ctx, &[&x_not_z, &y_not_z]),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    "||" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        let x_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &x,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        let y_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &y,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        z3::ast::Bool::ite(
                            &z3::ast::Bool::or(ctx, &[&x_not_z, &y_not_z]),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    "^" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        let x_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &x,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        let y_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &y,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        z3::ast::Bool::ite(
                            &z3::ast::Bool::xor(&x_not_z, &y_not_z),
                            &z3::ast::Int::from_i64(ctx, 1),
                            &z3::ast::Int::from_i64(ctx, 0),
                        )
                    }
                    "+" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Int::add(ctx, &[&x, &y])
                    }
                    "*" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Int::mul(ctx, &[&x, &y])
                    }
                    "/" => {
                        let l = sexpr_to_z3(ctx, tail[0]);
                        let r = sexpr_to_z3(ctx, tail[1]);
                        let zero = z3::ast::Int::from_i64(ctx, 0);

                        let l_neg = z3::ast::Int::lt(&l, &zero);
                        let r_neg = z3::ast::Int::lt(&r, &zero);

                        let l_abs = z3::ast::Bool::ite(&l_neg, &z3::ast::Int::unary_minus(&l), &l);
                        let r_abs = z3::ast::Bool::ite(&r_neg, &z3::ast::Int::unary_minus(&r), &r);
                        let div = z3::ast::Int::div(&l_abs, &r_abs);

                        let signs_differ = z3::ast::Bool::xor(&l_neg, &r_neg);

                        z3::ast::Bool::ite(
                            &r._eq(&zero),
                            &zero,
                            &z3::ast::Bool::ite(
                                &signs_differ,
                                &z3::ast::Int::unary_minus(&div),
                                &div,
                            ),
                        )
                    }
                    "%" => {
                        let l = sexpr_to_z3(ctx, tail[0]);
                        let r = sexpr_to_z3(ctx, tail[1]);
                        let zero = z3::ast::Int::from_i64(ctx, 0);
                        z3::ast::Bool::ite(
                            &r._eq(&zero),
                            &zero,
                            &z3::ast::Bool::ite(
                                &z3::ast::Bool::xor(
                                    &z3::ast::Int::lt(&l, &zero),
                                    &z3::ast::Int::lt(&r, &zero),
                                ),
                                &z3::ast::Int::unary_minus(&z3::ast::Int::div(
                                    &z3::ast::Bool::ite(
                                        &z3::ast::Int::lt(&l, &zero),
                                        &z3::ast::Int::unary_minus(&l),
                                        &l,
                                    ),
                                    &z3::ast::Bool::ite(
                                        &z3::ast::Int::lt(&r, &zero),
                                        &z3::ast::Int::unary_minus(&r),
                                        &r,
                                    ),
                                )),
                                &z3::ast::Int::modulo(&l, &r),
                            ),
                        )
                    }
                    "min" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Bool::ite(&z3::ast::Int::le(&x, &y), &x, &y)
                    }
                    "max" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        z3::ast::Bool::ite(&z3::ast::Int::le(&x, &y), &y, &x)
                    }
                    "select" => {
                        let x = sexpr_to_z3(ctx, tail[0]);
                        let y = sexpr_to_z3(ctx, tail[1]);
                        let z = sexpr_to_z3(ctx, tail[2]);
                        let x_not_z = z3::ast::Bool::not(&z3::ast::Int::_eq(
                            &x,
                            &z3::ast::Int::from_i64(ctx, 0),
                        ));
                        z3::ast::Bool::ite(&x_not_z, &y, &z)
                    }
                    _ => panic!("Unknown operator: {}", head),
                }
            }
        }
    }

    let mut cfg = z3::Config::new();
    cfg.set_timeout_msec(1000);
    let ctx = z3::Context::new(&cfg);
    let solver = z3::Solver::new(&ctx);
    let zero = z3::ast::Int::from_i64(&ctx, 0);
    let expr = sexpr_to_z3(&ctx, expr);

    // Check if expr == 0 is unsat (i.e., expr can never be false)
    solver.assert(&expr._eq(&zero));
    if matches!(solver.check(), z3::SatResult::Unsat) {
        return ValidationResult::Valid; // AlwaysTrue
    }
    solver.reset();

    // Check if expr != 0 is unsat (i.e., expr can never be true)
    solver.assert(&expr._eq(&zero).not());
    match solver.check() {
        z3::SatResult::Unsat => ValidationResult::Invalid,
        z3::SatResult::Unknown => ValidationResult::Unknown,
        z3::SatResult::Sat => ValidationResult::Unknown,
    }
}

pub fn compute_conditional_structures(
    conditional_soup: &Workload,
) -> (
    HashMap<Vec<bool>, Vec<Pattern<Pred>>>,
    Vec<Rewrite<Pred, SynthAnalysis>>,
) {
    let egraph: EGraph<Pred, SynthAnalysis> = conditional_soup.to_egraph();
    let mut pvec_to_terms: HashMap<Vec<bool>, Vec<Pattern<Pred>>> = HashMap::default();

    let cond_prop_ruleset = Pred::get_condition_propagation_rules(conditional_soup);

    for cond in conditional_soup.force() {
        let cond: RecExpr<Pred> = cond.to_string().parse().unwrap();
        let cond_pat = Pattern::from(&cond);

        let cond_id = egraph
            .lookup_expr(&cond_pat.to_string().parse().unwrap())
            .unwrap();

        let pvec = egraph[cond_id]
            .data
            .cvec
            .clone()
            .iter()
            .map(|b| *b != Some(0))
            .collect();

        pvec_to_terms
            .entry(pvec)
            .or_default()
            .push(cond_pat.clone());
    }

    (pvec_to_terms, cond_prop_ruleset)
}

/// Incrementally construct a ruleset by running rule inference up to a size bound,
/// using previously-learned rules at each step.
/// Importantly, this function is different from `recursive_rules_cond` in that it does not
/// actually generate the terms that it derives equivalences for.
pub fn soup_to_rules(
    soup: &Workload,
    conditions: Option<&Workload>,
    prior_rules: &Ruleset<Pred>,
    n: usize,
) -> Ruleset<Pred> {
    let (pvec_to_terms, cond_prop_ruleset) = if let Some(conditions) = conditions {
        // If we have a workload of conditions, compute the conditional structures
        // to help with rule inference.
        let (fst, snd) = compute_conditional_structures(&conditions);
        (Some(fst), Some(snd))
    } else {
        (None, None)
    };

    let mut ruleset = Ruleset::<Pred>::default();
    for i in 1..n {
        let workload = soup.clone().filter(Filter::MetricLt(Metric::Atoms, i + 1));

        if workload.force().is_empty() {
            continue;
        }

        let rules = run_workload(
            workload,
            prior_rules.clone(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
            pvec_to_terms.clone(),
            cond_prop_ruleset.clone(),
        );
        ruleset.extend(rules);
    }
    ruleset
}

pub fn recipe_to_rules(recipes: &Vec<Recipe>) -> Ruleset<Pred> {
    let mut ruleset: Ruleset<Pred> = Ruleset::default();
    for r in recipes {
        let rules = match &r.conditions {
            Some(c) => {
                let cond_lang = Lang {
                    vars: r.vars.clone(),
                    vals: c.vals.clone(),
                    ops: c.ops.clone(),
                };

                let base_lang = if cond_lang.ops.len() == 2 {
                    base_lang(2)
                } else {
                    base_lang(3)
                };

                let mut wkld = iter_metric(base_lang, "EXPR", Metric::Atoms, 3)
                    .filter(Filter::Contains("VAR".parse().unwrap()))
                    .plug("VAR", &Workload::new(cond_lang.vars))
                    .plug("VAL", &Workload::new(cond_lang.vals));
                for (i, ops) in cond_lang.ops.iter().enumerate() {
                    wkld = wkld.plug(format!("OP{}", i + 1), &Workload::new(ops));
                }

                // only want conditions greater than size 2
                wkld = wkld.filter(Filter::Invert(Box::new(Filter::MetricLt(Metric::Atoms, 2))));

                let (pvec_to_terms, cond_prop_ruleset) = compute_conditional_structures(&wkld);

                recursive_rules_cond(
                    Metric::Atoms,
                    r.max_size,
                    Lang {
                        vars: r.vars.clone(),
                        vals: r.vals.clone(),
                        ops: r.ops.clone(),
                    },
                    ruleset.clone(),
                    &pvec_to_terms,
                    &cond_prop_ruleset,
                )
            }
            None => recursive_rules(
                Metric::Atoms,
                r.max_size,
                Lang {
                    vars: r.vars.clone(),
                    vals: r.vals.clone(),
                    ops: r.ops.clone(),
                },
                ruleset.clone(),
            ),
        };
        ruleset.extend(rules);
    }
    ruleset
}

pub fn og_recipe() -> Ruleset<Pred> {
    let cond_lang = Lang::new(&["0"], &["a", "b", "c"], &[&[], &["<", "<=", "!="]]);

    let base_lang = if cond_lang.ops.len() == 2 {
        base_lang(2)
    } else {
        base_lang(3)
    };

    let mut wkld = iter_metric(base_lang, "EXPR", Metric::Atoms, 3)
        .filter(Filter::Contains("VAR".parse().unwrap()))
        .plug("VAR", &Workload::new(cond_lang.vars))
        .plug("VAL", &Workload::new(cond_lang.vals));
    for (i, ops) in cond_lang.ops.iter().enumerate() {
        wkld = wkld.plug(format!("OP{}", i + 1), &Workload::new(ops));
    }

    // only want conditions greater than size 2
    wkld = wkld.filter(Filter::Invert(Box::new(Filter::MetricLt(Metric::Atoms, 2))));

    let (pvec_to_terms, cond_prop_ruleset) = compute_conditional_structures(&wkld);
    let mut all_rules = Ruleset::default();

    let equality = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(&[], &["a", "b", "c"], &[&["!"], &["==", "!="]]),
        all_rules.clone(),
    );

    all_rules.extend(equality);

    let comparisons = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(&[], &["a", "b", "c"], &[&[], &["<", "<=", ">", ">="]]),
        all_rules.clone(),
    );

    all_rules.extend(comparisons);

    let bool_only = recursive_rules(
        Metric::Atoms,
        7,
        Lang::new(&[], &["a", "b", "c"], &[&["!"], &["&&", "||"]]),
        all_rules.clone(),
    );

    all_rules.extend(bool_only);

    // corresponds to "mul/div with constants + mul/div with constants and other arith"
    let arith_basic = recursive_rules_cond(
        Metric::Atoms,
        5,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[&[], &["+", "-", "*", "/", "%"]],
        ),
        all_rules.clone(),
        &pvec_to_terms,
        &cond_prop_ruleset,
    );

    all_rules.extend(arith_basic.clone());

    let min_max = recursive_rules(
        Metric::Atoms,
        7,
        Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max"]]),
        all_rules.clone(),
    );

    all_rules.extend(min_max);

    // the special workloads, which mostly revolve around
    // composing int2boolop(int_term, int_term) or things like that
    // together.
    //
    let int_lang = Lang::new(&[], &["a", "b", "c"], &[&[], &["+", "-", "min", "max"]]);

    let mut int_wkld = iter_metric(crate::recipe_utils::base_lang(2), "EXPR", Metric::Atoms, 3)
        .filter(Filter::Contains("VAR".parse().unwrap()))
        .plug("VAR", &Workload::new(int_lang.vars))
        .plug("VAL", &Workload::new(int_lang.vals))
        .append(Workload::new(&["0", "1"]));
    // let ops = vec![lang.uops, lang.bops, lang.tops];
    for (i, ops) in int_lang.ops.iter().enumerate() {
        int_wkld = int_wkld.plug(format!("OP{}", i + 1), &Workload::new(ops));
    }

    // for op in &["==", "<", "<=", ">", ">=", "||", "&&"] {
    for op in &["<", "<=", ">", ">="] {
        let big_wkld = Workload::new(&["0", "1"]).append(
            Workload::new(&["(OP V V)"])
                // okay: so we can't scale this up to multiple functions. we have to do the meta-recipe
                // thing where we have to basically feed in these operators one at a time.
                .plug("OP", &Workload::new(&[op]))
                .plug("V", &int_wkld)
                .filter(Filter::MetricLt(Metric::Atoms, 8)),
        );

        let wrapped_rules = run_workload(
            big_wkld,
            arith_basic.clone(), // and we gotta append min/max rules here too, to avoid `(max a a)`.
            Limits::synthesis(),
            Limits {
                iter: 1,
                node: 100_000,
                match_: 100_000,
            },
            true,
            Some(pvec_to_terms.clone()),
            Some(cond_prop_ruleset.clone()),
        );

        all_rules.extend(wrapped_rules);
    }

    all_rules
}

pub fn og_recipe_no_conditions() -> Ruleset<Pred> {
    let mut all_rules = Ruleset::default();

    let equality = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(&[], &["a", "b", "c"], &[&["!"], &["==", "!="]]),
        all_rules.clone(),
    );

    all_rules.extend(equality);

    let comparisons = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(&[], &["a", "b", "c"], &[&[], &["<", "<=", ">", ">="]]),
        all_rules.clone(),
    );

    all_rules.extend(comparisons);

    let bool_only = recursive_rules(
        Metric::Atoms,
        7,
        Lang::new(&[], &["a", "b", "c"], &[&["!"], &["&&", "||"]]),
        all_rules.clone(),
    );

    all_rules.extend(bool_only);

    // corresponds to "mul/div with constants + mul/div with constants and other arith"
    let arith_basic = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[&[], &["+", "-", "*", "/", "%"]],
        ),
        all_rules.clone(),
    );

    all_rules.extend(arith_basic.clone());

    let min_max = recursive_rules(
        Metric::Atoms,
        7,
        Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max"]]),
        all_rules.clone(),
    );

    all_rules.extend(min_max);

    // the special workloads, which mostly revolve around
    // composing int2boolop(int_term, int_term) or things like that
    // together.
    //
    let int_lang = Lang::new(&[], &["a", "b", "c"], &[&[], &["+", "-", "min", "max"]]);

    let mut int_wkld = iter_metric(crate::recipe_utils::base_lang(2), "EXPR", Metric::Atoms, 3)
        .filter(Filter::Contains("VAR".parse().unwrap()))
        .plug("VAR", &Workload::new(int_lang.vars))
        .plug("VAL", &Workload::new(int_lang.vals))
        .append(Workload::new(&["0", "1"]));
    // let ops = vec![lang.uops, lang.bops, lang.tops];
    for (i, ops) in int_lang.ops.iter().enumerate() {
        int_wkld = int_wkld.plug(format!("OP{}", i + 1), &Workload::new(ops));
    }

    // for op in &["==", "<", "<=", ">", ">=", "||", "&&"] {
    for op in &["<", "<=", ">", ">="] {
        let big_wkld = Workload::new(&["0", "1"]).append(
            Workload::new(&["(OP V V)"])
                // okay: so we can't scale this up to multiple functions. we have to do the meta-recipe
                // thing where we have to basically feed in these operators one at a time.
                .plug("OP", &Workload::new(&[op]))
                .plug("V", &int_wkld)
                .filter(Filter::MetricLt(Metric::Atoms, 8)),
        );

        let wrapped_rules = run_workload(
            big_wkld,
            arith_basic.clone(), // and we gotta append min/max rules here too, to avoid `(max a a)`.
            Limits::synthesis(),
            Limits {
                iter: 1,
                node: 100_000,
                match_: 100_000,
            },
            true,
            None,
            None,
        );

        all_rules.extend(wrapped_rules);
    }

    all_rules
}
