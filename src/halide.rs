use std::str::FromStr;

use crate::{
    conditions::{
        assumption::Assumption,
        implication::{Implication, ImplicationValidationResult},
        implication_set::run_implication_workload,
    },
    enumo::Rule,
    recipe_utils::{base_lang, iter_metric},
    time_fn_call, *,
};

use conditions::implication_set::ImplicationSet;
use egg::{RecExpr, Rewrite, Runner};
use enumo::{Filter, Metric, Ruleset, Sexp, Workload};
use num::ToPrimitive;
use recipe_utils::{recursive_rules_cond, run_workload, Lang};
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
    "assume" = Assume(Id),
    Var(Symbol),
  }
}

impl Pred {
    pub fn get_condition_propagation_rules(
        conditions: &Workload,
    ) -> Vec<Rewrite<Self, SynthAnalysis>> {
        let forced = conditions.force();

        let mut result: Vec<Rewrite<Self, SynthAnalysis>> = vec![];
        for c in &forced {
            let c_recexpr: RecExpr<Self> = c.to_string().parse().unwrap();
            let c_pat = Pattern::from(&c_recexpr.clone());
            // pairwise checking implication of all conditions
            for c2 in &forced {
                if c == c2 {
                    continue;
                }
                let c2_recexpr: RecExpr<Self> = c2.to_string().parse().unwrap();
                let c2_pat = Pattern::from(&c2_recexpr.clone());
                let c_vars = c_pat.vars();
                let c2_vars = c2_pat.vars();

                if c2_vars.iter().any(|v| !c_vars.contains(v)) {
                    // can't have variables on the right that are not on the left.
                    continue;
                }

                let rw = ImplicationSwitch {
                    parent_cond: c_pat.clone(),
                    my_cond: c2_pat.clone(),
                }
                .rewrite();

                println!("c_pat: {c_pat}");
                println!("c2_pat: {c2_pat}");

                let imp: Result<Implication<Pred>, _> = Implication::new(
                    format!("{c_pat} -> {c2_pat}").into(),
                    Assumption::new(c_pat.to_string()).unwrap(),
                    Assumption::new(c2_pat.to_string()).unwrap(),
                );

                if let Err(e) = &imp {
                    assert!(e.to_string().contains("contains variables"));
                    continue;
                }

                let imp = imp.unwrap();

                if imp.is_valid() && !result.iter().any(|r| r.name == rw.name)
                // avoid duplicates
                {
                    result.push(rw);
                }
            }
        }
        result
    }
}

impl SynthLanguage for Pred {
    type Constant = Constant;

    fn name() -> &'static str {
        "Halide"
    }

    fn egglog_lang_def() -> String {
        let name = Self::name();
        format!(
            r#"
            (datatype {name})
            (constructor Lit (i64) {name})
            (constructor Abs ({name}) {name})
            (constructor Lt ({name} {name}) {name})
            (constructor Leq ({name} {name}) {name})
            (constructor Gt ({name} {name}) {name})
            (constructor Geq ({name} {name}) {name})
            (constructor Eq ({name} {name}) {name})
            (constructor Neq ({name} {name}) {name})
            (constructor Implies ({name} {name}) {name})
            (constructor Not ({name}) {name})
            (constructor Neg ({name}) {name})
            (constructor And ({name} {name}) {name})
            (constructor Or ({name} {name}) {name})
            (constructor Xor ({name} {name}) {name})
            (constructor Add ({name} {name}) {name})
            (constructor Sub ({name} {name}) {name})
            (constructor Mul ({name} {name}) {name})
            (constructor Div ({name} {name}) {name})
            (constructor Mod ({name} {name}) {name})
            (constructor Min ({name} {name}) {name})
            (constructor Max ({name} {name}) {name})
            (constructor Select ({name} {name} {name}) {name})
            (constructor Var (String) {name})
        "#
        )
    }

    fn to_bool(c: Self::Constant) -> Option<bool> {
        // This is a pretty stringent definition of what
        // it means to be true.
        match c {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    fn to_egglog_term(pat: Pattern<Self>) -> String {
        // TODO(@ninehusky):
        // we can do something probably where we take the pattern,
        // convert it to a RecExpr (AST), and "interpret" it backwards.
        // that seems easy to mess up, so we'll do it a bad way for now.
        pub fn sexp_to_egglog(term: &Sexp) -> Sexp {
            match term {
                Sexp::Atom(a) => {
                    if let Ok(num) = a.parse::<i64>() {
                        Sexp::Atom(format!("(Lit {num})"))
                    } else if a.starts_with("?") {
                        // a is a meta-variable, leave it alone.
                        Sexp::Atom(a.into())
                    } else {
                        Sexp::Atom(format!("(Var \"{a}\")"))
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
                        new_list.push(sexp_to_egglog(item));
                    }
                    Sexp::List(new_list)
                }
            }
        }
        let sexp: Sexp = Sexp::from_str(&pat.to_string()).unwrap();
        sexp_to_egglog(&sexp).to_string()
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
            Pred::Assume(_) => {
                // TODO: @ninehusky - I actually kind of want to panic here, because
                // cvec matching on `assume` is just a bad thing waiting to happen.
                // I'm actually not sure what a more principled fix would be, however,
                // so leaving it as is for now. Maybe we can kick the can to later --
                // if a rule is generated with `assume`, we can panic then?
                vec![None, None, None]
            }
        }
    }

    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]) {
        let mut vars: Vec<_> = vars.into();
        vars.sort();

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

    fn is_assumption(&self) -> bool {
        matches!(self, Pred::Assume(_))
    }

    fn is_predicate(&self) -> bool {
        matches!(
            self,
            Pred::And(_)
                | Pred::Or(_)
                | Pred::Not(_)
                | Pred::Lt(_)
                | Pred::Leq(_)
                | Pred::Gt(_)
                | Pred::Geq(_)
                | Pred::Eq(_)
                | Pred::Neq(_)
        )
    }

    fn validate_implication(imp: Implication<Pred>) -> ImplicationValidationResult {
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);

        let lexpr: Pattern<Pred> = imp.lhs().clone().chop_assumption();
        let rexpr: Pattern<Pred> = imp.rhs().clone().chop_assumption();

        // chop off the assumptions, by taking everything except the last element.
        // we should definitely test this.
        let lexpr = egg_to_z3(&ctx, Pred::instantiate(&lexpr).as_ref());
        let rexpr = egg_to_z3(&ctx, Pred::instantiate(&rexpr).as_ref());

        let zero = z3::ast::Int::from_i64(&ctx, 0);
        let one = z3::ast::Int::from_i64(&ctx, 1);

        // ask the solver to find a model where the LHS is true.
        solver.assert(&lexpr._eq(&zero).not());

        // if it can't, then the LHS is trivially false
        if matches!(solver.check(), z3::SatResult::Unsat) {
            return ImplicationValidationResult::LhsFalse;
        }

        solver.reset();

        // ask the solver to find a model where the RHS is false.
        solver.assert(&one._eq(&rexpr).not());

        // if it can't, then the RHS is trivially true.
        if matches!(solver.check(), z3::SatResult::Unsat) {
            return ImplicationValidationResult::RhsTrue;
        }

        solver.reset();
        solver.assert(
            &z3::ast::Bool::implies(&lexpr._eq(&zero).not(), &rexpr._eq(&zero).not()).not(),
        );

        let result = solver.check();

        match result {
            z3::SatResult::Unsat => ImplicationValidationResult::NonTrivialValid,
            z3::SatResult::Unknown => ImplicationValidationResult::Unknown,
            z3::SatResult::Sat => ImplicationValidationResult::Invalid,
        }
    }

    // fn condition_implies(
    //     lhs: &Pattern<Self>,
    //     rhs: &Pattern<Self>,
    //     cache: &mut HashMap<(String, String), bool>,
    // ) -> bool {
    //     let lhs_str = lhs.to_string();
    //     let rhs_str = rhs.to_string();
    //     if cache.contains_key(&(lhs_str.clone(), rhs_str.clone())) {
    //         return *cache.get(&(lhs_str, rhs_str)).unwrap();
    //     }

    //     let mut cfg = z3::Config::new();
    //     cfg.set_timeout_msec(1000);
    //     let ctx = z3::Context::new(&cfg);
    //     let solver = z3::Solver::new(&ctx);
    //     let zero = z3::ast::Int::from_i64(&ctx, 0);

    //     // given that the lhs is true, can we make the rhs false?

    //     let lhs = egg_to_z3(&ctx, Self::instantiate(lhs).as_ref())
    //         ._eq(&zero)
    //         .not();

    //     let rhs = egg_to_z3(&ctx, Self::instantiate(rhs).as_ref())
    //         ._eq(&zero)
    //         .not();

    //     let assertion = &lhs;

    //     solver.assert(assertion);

    //     if matches!(solver.check(), z3::SatResult::Unsat) {
    //         // don't want something that is always false
    //         cache.insert((lhs_str, rhs_str), false);
    //         return false;
    //     }

    //     solver.reset();
    //     let assertion = &rhs;

    //     solver.assert(&assertion.not());

    //     if matches!(solver.check(), z3::SatResult::Unsat) {
    //         // don't want something that is always true
    //         cache.insert((lhs_str, rhs_str), false);
    //         return false;
    //     }

    //     solver.reset();

    //     let assertion = &z3::ast::Bool::implies(&lhs, &rhs).not();

    //     solver.assert(assertion);

    //     let res = solver.check();
    //     let implies = matches!(res, z3::SatResult::Unsat);
    //     cache.insert((lhs_str, rhs_str), implies);
    //     implies
    // }

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
        cond: &Assumption<Self>,
    ) -> ValidationResult {
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let zero = z3::ast::Int::from_i64(&ctx, 0);

        let cond: Pattern<Self> = cond.chop_assumption();

        let cexpr =
            z3::ast::Bool::not(&egg_to_z3(&ctx, Self::instantiate(&cond).as_ref())._eq(&zero));

        let lexpr = egg_to_z3(&ctx, Self::instantiate(lhs).as_ref());
        let rexpr = egg_to_z3(&ctx, Self::instantiate(rhs).as_ref());
        solver.assert(&z3::ast::Bool::implies(&cexpr, &lexpr._eq(&rexpr)).not());

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
                let rem = z3::ast::Int::rem(&l_abs, &r_abs);

                let signs_differ = z3::ast::Bool::xor(&l_neg, &r_neg);

                buf.push(z3::ast::Bool::ite(
                    &r._eq(&zero),
                    &zero,
                    &z3::ast::Bool::ite(&signs_differ, &z3::ast::Int::unary_minus(&rem), &rem),
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
            Pred::Assume(_) => {
                panic!("assumption nodes should not be used in egg_to_z3");
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
                                &z3::ast::Int::rem(&l, &r),
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
    let result = solver.check();
    if matches!(result, z3::SatResult::Unsat) {
        return ValidationResult::Invalid; // AlwaysFalse
    } else if matches!(result, z3::SatResult::Unknown) {
        return ValidationResult::Unknown;
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

pub fn og_recipe() -> Ruleset<Pred> {
    log::info!("LOG: Starting recipe.");
    let start_time = std::time::Instant::now();
    let wkld = conditions::generate::get_condition_workload();
    let mut all_rules = Ruleset::default();
    let mut base_implications = ImplicationSet::default();
    // and the "and" rules here.
    let and_implies_left: Implication<Pred> = Implication::new(
        "and_implies_left".into(),
        Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
        Assumption::new_unsafe("?a".to_string()).unwrap(),
    )
    .unwrap();

    let and_implies_right: Implication<Pred> = Implication::new(
        "and_implies_right".into(),
        Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
        Assumption::new_unsafe("?b".to_string()).unwrap(),
    )
    .unwrap();

    base_implications.add(and_implies_left);
    base_implications.add(and_implies_right);

    let other_implications = time_fn_call!(
        "find_base_implications",
        run_implication_workload(
            &wkld,
            &["a".to_string(), "b".to_string(), "c".to_string()],
            &base_implications,
            &Default::default()
        )
    );

    base_implications.add_all(other_implications);

    println!("# base implications: {}", base_implications.len());

    for i in base_implications.iter() {
        println!("implication: {}", i.name());
    }
    // here, make sure wkld is non empty
    assert_ne!(wkld, Workload::empty());

    let simp_comps = time_fn_call!(
        "simp_comps",
        recursive_rules_cond(
            Metric::Atoms,
            5,
            Lang::new(&["0", "1"], &["a", "b", "c"], &[&[], &["<", ">", "+", "-"]]),
            Ruleset::default(),
            base_implications.clone(),
            wkld.clone(),
        )
    );

    all_rules.extend(simp_comps.clone());

    let arith_basic = time_fn_call!(
        "arith_basic",
        recursive_rules_cond(
            Metric::Atoms,
            5,
            Lang::new(
                &["0", "1"],
                &["a", "b", "c"],
                &[&["-"], &["+", "-", "*", "/"]],
            ),
            Ruleset::default(),
            base_implications.clone(),
            wkld.clone(),
        )
    );
    all_rules.extend(arith_basic.clone());

    let min_max = time_fn_call!(
        "min_max",
        recursive_rules_cond(
            Metric::Atoms,
            7,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max"]]),
            all_rules.clone(),
            base_implications.clone(),
            wkld.clone(),
        )
    );

    all_rules.extend(min_max.clone());

    let min_max_add = time_fn_call!(
        "min_max_add",
        recursive_rules_cond(
            Metric::Atoms,
            5,
            Lang::new(&["0", "1"], &["a", "b", "c"], &[&[], &["+", "min", "max"]]),
            all_rules.clone(),
            base_implications.clone(),
            wkld.clone(),
        )
    );

    all_rules.extend(min_max_add.clone());

    for op in &["min", "max"] {
        let int_workload =
            // i only want OP2s and EXPRs
            iter_metric(base_lang(2), "EXPR", Metric::Atoms, 5).filter(Filter::And(vec![
                Filter::Excludes("VAL".parse().unwrap()),
                Filter::Excludes("OP1".parse().unwrap()),
            ]))
            .plug("OP2", &Workload::new(&[op, "+"]))
            .plug("VAR", &Workload::new(&["a", "b", "c", "d"]));

        let lt_workload =
            Workload::new(&["(< V V)"])
                .plug("V", &int_workload)
                .filter(Filter::Canon(vec![
                    "a".to_string(),
                    "b".to_string(),
                    "c".to_string(),
                    "d".to_string(),
                ]));

        let lt_rules = time_fn_call!(
            format!("lt_rules_{}", op),
            run_workload(
                lt_workload,
                Some(Workload::new(&[
                    "(< a 0)", "(> a 0)", "(!= b c)", "(!= c d)"
                ])),
                all_rules.clone(),
                base_implications.clone(),
                Limits::synthesis(),
                Limits::minimize(),
                true,
            )
        );
        all_rules.extend(lt_rules);
    }

    let mut dummy_ruleset: Ruleset<Pred> = Ruleset::default();
    dummy_ruleset.add(
        Rule::from_string(
            "(< (min ?z ?y) (min ?x (+ ?y ?c0))) ==> (< (min ?z ?y) ?x) if (> ?c0 0)",
        )
        .unwrap()
        .0,
    );
    dummy_ruleset.add(
        Rule::from_string(
            "(< (max ?z (+ ?y ?c0)) (max ?x ?y)) ==> (< (max ?z (+ ?y ?c0)) ?x) if (> ?c0 0)",
        )
        .unwrap()
        .0,
    );
    dummy_ruleset.add(
        Rule::from_string(
            "(< (min ?z (+ ?y ?c0)) (min ?x ?y)) ==> (< (min ?z (+ ?y ?c0)) ?x) if (< ?c0 0)",
        )
        .unwrap()
        .0,
    );
    dummy_ruleset.add(
        Rule::from_string(
            "(< (max ?z ?y) (max ?x (+ ?y ?c0))) ==> (< (max ?z ?y) ?x) if (< ?c0 0)",
        )
        .unwrap()
        .0,
    );
    dummy_ruleset.add(
        Rule::from_string("(< (min ?x ?y) (+ ?x ?c0)) ==> 1 if (> ?c0 0)")
            .unwrap()
            .0,
    );
    // dummy_ruleset.add(
    //     Rule::from_string("(< (max ?a ?c) (min ?a ?b)) ==> 0")
    //         .unwrap()
    //         .0,
    // );

    let mut cannot_derive = vec![];
    for r in dummy_ruleset.iter() {
        assert!(r.is_valid());
        if !all_rules.can_derive_cond(
            DeriveType::LhsAndRhs,
            r,
            Limits::deriving(),
            &base_implications.to_egg_rewrites(),
        ) {
            cannot_derive.push(r);
        } else {
            println!("I was able to derive: {}", r);
        }
    }

    assert!(
        cannot_derive.is_empty(),
        "Could not derive: {:?}",
        cannot_derive
    );

    for op in &["min", "max"] {
        let int_workload = Workload::new(&["0", "1", "(OP V V)"])
            .plug("OP", &Workload::new(&[op]))
            .plug("V", &Workload::new(&["a", "b", "c"]));

        let eq_workload = Workload::new(&["0", "1", "(OP V V)"])
            .plug("OP", &Workload::new(&["=="]))
            .plug("V", &int_workload)
            .filter(Filter::Canon(vec![
                "a".to_string(),
                "b".to_string(),
                "c".to_string(),
            ]));

        let eq_simp = time_fn_call!(
            format!("eq_simp_{}", op),
            run_workload(
                eq_workload,
                Some(wkld.clone()),
                min_max.clone(),
                base_implications.clone(),
                Limits::synthesis(),
                Limits::minimize(),
                true,
            )
        );

        all_rules.extend(eq_simp);
    }

    let min_max_mul = time_fn_call!(
        "min_max_mul",
        recursive_rules_cond(
            Metric::Atoms,
            7,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "*"]]),
            all_rules.clone(),
            base_implications.clone(),
            wkld.clone(),
        )
    );

    all_rules.extend(min_max_mul);

    // let min_max_div = recursive_rules_cond(
    //     Metric::Atoms,
    //     7,
    //     Lang::new(&["0", "1"], &["a", "b", "c"], &[&[], &["min", "max", "/"]]),
    //     all_rules.clone(),
    //     wkld.clone(),
    // );

    // all_rules.extend(min_max_div);

    let end_time = std::time::Instant::now();

    all_rules.pretty_print();

    println!(
        "finished recipe (seconds: {})",
        end_time.duration_since(start_time).as_secs_f64()
    );

    all_rules
}

#[test]
fn im_suspicious() {
    let wkld = conditions::generate::get_condition_workload();
    let mut base_implications = ImplicationSet::default();
    // and the "and" rules here.
    let and_implies_left: Implication<Pred> = Implication::new(
        "and_implies_left".into(),
        Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
        Assumption::new_unsafe("?a".to_string()).unwrap(),
    )
    .unwrap();

    let and_implies_right: Implication<Pred> = Implication::new(
        "and_implies_right".into(),
        Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
        Assumption::new_unsafe("?b".to_string()).unwrap(),
    )
    .unwrap();

    base_implications.add(and_implies_left);
    base_implications.add(and_implies_right);

    let other_implications = time_fn_call!(
        "find_base_implications",
        run_implication_workload(
            &wkld,
            &["a".to_string(), "b".to_string(), "c".to_string()],
            &base_implications,
            &Default::default()
        )
    );

    base_implications.add_all(other_implications);

    println!("# base implications: {}", base_implications.len());
    let rules = r#"(< 0 ?a) <=> (> ?a 0)
(< 1 ?a) <=> (> ?a 1)
(> 0 ?a) <=> (< ?a 0)
(+ 1 ?a) <=> (+ ?a 1)
(> 1 ?a) <=> (< ?a 1)
(+ 0 ?a) <=> (+ ?a 0)
(+ 0 ?a) <=> (- ?a 0)
(< ?a ?b) <=> (> ?b ?a)
(> ?a ?a) <=> (- ?a ?a)
(+ ?a ?b) <=> (+ ?b ?a)
?a <=> (+ 0 ?a)
(> ?a ?a) ==> 0
(< ?b ?a) ==> 0 if (<= ?a ?b)
(< ?b ?a) ==> 0 if (< ?a ?b)
(< ?b ?a) ==> 1 if (< ?b ?a)
(< 1 ?a) ==> 0 if (<= ?a 0)
(< ?a 1) ==> 1 if (<= ?a 0)
(< ?a 0) <=> (< ?a 1) if  (< 0 ?a)
(< 0 ?a) ==> 0 if (< ?a 0)
(< 1 ?a) ==> 0 if (< ?a 0)
(< ?a 1) ==> 1 if (< ?a 0)
(< 0 ?a) <=> (< 1 ?a) if  (<= ?a 0)
(< ?b ?a) ==> 0 if (== ?a ?b)
(+ ?a ?b) ==> ?a if (== ?b 0)
(< ?a 0) <=> (< ?a 1) if  (< ?a 0)
(< 0 ?a) <=> (< 1 ?a) if  (< ?a 0)
(+ ?b ?a) ==> (+ ?a ?a) if (== ?b ?a)
(+ ?b ?a) ==> (+ ?b ?b) if (== ?b ?a)
(- ?a ?b) <=> (- ?b ?a) if  (== ?b ?a)
(< ?a ?b) <=> (< ?b ?a) if  (== ?b ?a)
(< ?a 1) <=> (+ ?a 1) if  (== ?a 0)
(< ?a 1) <=> (- 1 ?a) if  (== ?a 0)
(< ?a 0) <=> (< 0 ?a) if  (== ?a 0)
(< ?a 0) <=> (- 0 ?a) if  (== ?a 0)
(- 0 ?a) <=> (< 1 ?a) if  (== ?a 0)
(< ?a ?b) ==> (< ?a 0) if (== ?b 0)
(+ ?a ?a) <=> (< 1 ?a) if  (== ?a 0)
(- ?b ?a) ==> (- 0 ?a) if (== ?b 0)
(< ?b ?a) ==> (< 0 ?a) if (== ?b 0)
(+ ?b ?a) <=> (- ?a ?b) if  (== ?b 0)
(- ?b ?a) <=> (< ?b ?a) if  (== ?a ?b)
(< ?a 1) <=> (< ?a 0) if  (!= ?a 0)
(+ ?c (+ ?b ?a)) <=> (+ ?a (+ ?c ?b))
(< ?c (- ?b ?a)) <=> (< (+ ?c ?a) ?b)
(< ?a (- ?b ?a)) <=> (< (+ ?a ?a) ?b)
(+ ?b (+ ?b ?a)) <=> (+ ?a (+ ?b ?b))
(- ?c (+ ?b ?a)) <=> (- (- ?c ?a) ?b)
(- (+ ?c ?b) ?a) <=> (+ ?b (- ?c ?a))
(< ?c (+ ?b ?a)) <=> (< (- ?c ?a) ?b)
(- ?c (- ?b ?a)) <=> (- (+ ?c ?a) ?b)
(< ?b (< 0 ?a)) <=> (< ?b (< ?b ?a))
(< (< ?b 1) ?a) <=> (< (< ?b ?a) ?a)
(< (< 1 ?b) ?a) <=> (< (< ?a ?b) ?a)
(< ?a (< ?b 0)) <=> (< ?a (< ?b ?a))
(- ?b (- ?b ?a)) ==> (+ ?a (< 1 0))
(+ ?a (- ?b ?a)) ==> (- ?b (< 1 0))
(- (+ ?b ?a) ?a) ==> (- ?b (< 1 0))
(< ?b (- ?b ?a)) ==> (< 0 (- 0 ?a))
(+ ?b (- 1 ?a)) <=> (- 1 (- ?a ?b))
(- 1 (- ?b ?a)) <=> (+ (- ?a ?b) 1)
(- 1 (- ?b ?a)) <=> (- (+ ?a 1) ?b)
(- 1 (- ?b ?a)) <=> (- ?a (- ?b 1))
(- ?b (+ ?a 1)) <=> (- (- ?b 1) ?a)
(- (- ?b ?a) 1) <=> (- (- ?b 1) ?a)
(< (+ ?a ?b) ?b) ==> (< ?a (< 1 0))
(< 0 (< ?b ?a)) <=> (< 0 (- ?a ?b))
(- ?b (- 1 ?a)) <=> (+ ?a (- ?b 1))
(- ?b (- 1 ?a)) <=> (- ?a (- 1 ?b))
(< (- ?b ?a) 0) <=> (< 0 (- ?a ?b))
(< (+ ?b ?a) 0) <=> (< ?a (- 0 ?b))
(< ?b (+ ?a 1)) <=> (- 1 (< ?a ?b))
(< (< ?b ?a) 1) <=> (< (- ?a ?b) 1)
(< (- ?b ?a) 1) <=> (- 1 (< ?a ?b))
(< ?a (+ ?b ?a)) ==> (< (< 1 0) ?b)
(< (- ?b ?a) ?b) ==> (- 1 (< ?a 1))
(- (+ ?b ?a) 1) <=> (+ ?a (- ?b 1))
(- ?b (+ ?a ?b)) ==> (- (< 1 0) ?a)
(- (- ?a ?b) ?a) ==> (- 1 (+ ?b 1))
(< 1 (+ ?b ?a)) <=> (< (- 1 ?a) ?b)
(- 1 (< ?b ?a)) <=> (< (- ?a 1) ?b)
(- 1 (+ ?b ?a)) <=> (- (- 1 ?a) ?b)
(- 1 (- ?a 1)) <=> (- (+ 1 1) ?a)
(- 1 (- ?a 1)) <=> (+ 1 (- 1 ?a))
(- ?a (+ 1 1)) <=> (- (- ?a 1) 1)
(- 0 (- 1 ?a)) <=> (+ ?a (- 0 1))
(- 0 (- 1 ?a)) <=> (- ?a (< 0 1))
(- 1 (- 0 ?a)) <=> (- ?a (- 0 1))
(- 1 (- 0 ?a)) <=> (+ ?a (< 0 1))
(+ 1 (- 0 ?a)) <=> (- (< 0 1) ?a)
(+ 1 (- 0 ?a)) <=> (- 0 (- ?a 1))
(< ?a (+ 1 1)) <=> (< (- ?a 1) 1)
(< ?a (+ 1 1)) <=> (- 1 (< 1 ?a))
(< ?a (+ 1 1)) <=> (< (< 1 ?a) 1)
(- (- 0 1) ?a) <=> (- (- 0 ?a) 1)
(- (- 0 1) ?a) <=> (- 0 (+ ?a 1))
(- (- 1 ?a) 1) <=> (- (< 1 0) ?a)
(- (- 1 ?a) 1) <=> (- 1 (+ ?a 1))
(< 1 (- ?a 1)) <=> (< (+ 1 1) ?a)
(- 0 (< ?a 1)) <=> (- (< 0 ?a) 1)
(< (+ ?a 1) 0) <=> (< ?a (- 0 1))
(< (+ ?a 1) 0) <=> (< 1 (- 0 ?a))
(< (< ?a 0) 1) <=> (< 0 (+ ?a 1))
(< (< ?a 0) 1) <=> (- 1 (< ?a 0))
(< (< ?a 0) 1) <=> (< (- 0 ?a) 1)
(< (< ?a 0) 1) <=> (< (- 0 1) ?a)
(+ ?a (+ 1 1)) <=> (+ 1 (+ ?a 1))
(- 0 (< 0 ?a)) <=> (- (< ?a 1) 1)
(< ?a (< 0 1)) <=> (< 0 (< ?a 1))
(< ?a (< 0 1)) <=> (- 1 (< 0 ?a))
(< ?a (< 0 1)) <=> (< 0 (- 1 ?a))
(< ?a (< 0 1)) <=> (< (< 0 ?a) 1)
(< ?a (< 0 1)) <=> (< (- ?a 1) 0)
(< 0 (- 0 ?a)) <=> (< (+ ?a 1) 1)
(< 0 (- 0 ?a)) <=> (< 1 (- 1 ?a))
(< 0 (- 0 ?a)) <=> (< 0 (< ?a 0))
(< 0 (- 0 ?a)) <=> (< ?a (< 1 0))
(< 1 (< ?a 1)) <=> (< (< 0 ?a) 0)
(< (< 0 ?a) 0) <=> (< (< ?a 0) 0)
(< 1 (< ?a 1)) <=> (< 1 (< ?a 0))
(< (< 0 ?a) 0) <=> (< 1 (< 1 ?a))
(< (< 0 ?a) 0) <=> (< 1 (< 0 ?a))
(< (< 0 ?a) 0) <=> (< (< 1 ?a) 0)
(< 1 (< ?a 1)) <=> (< (< ?a 1) 0)
(< (- 0 ?a) 0) <=> (< (- 1 ?a) 1)
(< (- 0 ?a) 0) <=> (- 1 (< ?a 1))
(< (- 0 ?a) 0) <=> (< 0 (< 0 ?a))
(< (- 0 ?a) 0) <=> (< (< ?a 1) 1)
(< (- 0 ?a) 0) <=> (< 1 (+ ?a 1))
(< (- 0 ?a) 0) <=> (< (< 1 0) ?a)
(< (- 1 ?a) 0) <=> (< 0 (< 1 ?a))
(< (- 1 ?a) 0) <=> (< (< 0 1) ?a)
(< (- 1 ?a) 0) <=> (< 0 (- ?a 1))
(+ ?a (< 1 0)) <=> (- (+ ?a 1) 1)
(+ ?a (< 1 0)) <=> (+ 1 (- ?a 1))
(+ ?a (< 1 0)) <=> (- 0 (- 0 ?a))
(+ ?a (< 1 0)) <=> (- 1 (- 1 ?a))
(< ?a (- 1 ?a)) <=> (< ?a (< 0 1))
(< (+ ?a ?a) 1) <=> (< ?a (< 0 1))
(< ?a (< ?a 1)) <=> (< ?a (< 0 1))
(< ?a (< 1 ?a)) <=> (< 0 (- 0 ?a))
(< (+ ?a ?a) 0) <=> (< 0 (- 0 ?a))
(< ?a (< 0 ?a)) <=> (< 0 (- 0 ?a))
(< ?a (- 0 ?a)) <=> (< 0 (- 0 ?a))
(< ?a (< ?a 0)) <=> (< 0 (- 0 ?a))
(< 1 (< ?a ?b)) ==> (< 1 (< ?a 1))
(+ ?a (- 0 ?a)) <=> (< 1 (< ?a 1))
(< (+ ?a 1) ?a) <=> (< (< 0 ?a) 0)
(< ?a (- ?a 1)) <=> (< 1 (< ?a 1))
(< (< ?a ?b) 0) ==> (< (< ?a 0) 0)
(< 0 (+ ?a ?a)) <=> (< (- 0 ?a) 0)
(< (< ?a 1) ?a) <=> (< (- 0 ?a) 0)
(< 1 (+ ?a ?a)) <=> (< (- 0 ?a) 0)
(< (< 1 ?a) ?a) <=> (< (- 0 ?a) 0)
(< (- 1 ?a) ?a) <=> (< (- 0 ?a) 0)
(< (- 0 ?a) ?a) <=> (< (- 0 ?a) 0)
(< (< ?a 0) ?a) <=> (< (- 0 ?a) 0)
(< (< 0 ?a) ?a) <=> (< (- 1 ?a) 0)
(- (- 0 ?a) ?a) <=> (- 0 (+ ?a ?a))
(< (+ ?a 1) ?b) <=> (< 1 (- ?b ?a))
(- (- 1 ?a) ?a) <=> (- 1 (+ ?a ?a))
(+ (+ ?a ?a) 1) <=> (+ ?a (+ ?a 1))
(< (- 0 ?a) ?b) <=> (< 0 (+ ?b ?a))
(< ?a (- ?b 1)) <=> (< 1 (- ?b ?a))
(+ ?a (+ ?b 1)) <=> (+ (+ ?b ?a) 1)
(< (+ ?a ?b) 1) <=> (< ?b (- 1 ?a))
(- ?a (- ?a 1)) <=> (< (- ?a 1) ?a)
(< (- ?a 1) ?a) <=> (< ?a (+ ?a 1))
(- ?a (- ?a 1)) <=> (- (+ ?a 1) ?a)
(< (- ?a 1) ?a) <=> (+ ?a (- 1 ?a))
(- (+ ?a ?a) 1) <=> (+ ?a (- ?a 1))
(- (+ ?a ?a) 1) <=> (- ?a (- 1 ?a))
(- (- ?a 1) ?a) <=> (- ?a (+ ?a 1))
(- ?a (- 0 ?b)) <=> (- ?b (- 0 ?a))
(- (- 0 ?a) ?b) <=> (- 0 (+ ?b ?a))
(- 0 (- ?a ?b)) <=> (+ ?b (- 0 ?a))
(< (< 0 ?b) ?a) <=> (< (< ?a ?b) ?a) if  (!= ?b ?a)
(< ?a (< ?b 1)) <=> (< ?a (< ?b ?a)) if  (!= ?a ?b)
(< ?b (< ?a 1)) <=> (< ?b (< ?a 0)) if  (!= ?a ?b)
(- (< ?a ?b) 1) <=> (- 0 (< ?b ?a)) if  (!= ?b ?a)
(- 0 (< ?b ?a)) <=> (- (< ?a ?b) 1) if  (!= ?a ?b)
(< ?b (< ?c ?a)) ==> (< ?b (< 1 ?a)) if (!= ?b 0)
(< ?c (< ?b ?a)) ==> (< ?c (< ?b 1)) if (!= ?c 0)
(< ?b (< 1 ?a)) <=> (< ?b (< ?a 0)) if  (!= ?b 0)
(< ?b (< 0 ?a)) <=> (< ?b (< ?a 1)) if  (!= ?b 0)
(< ?b (< 1 ?a)) <=> (< ?b (< ?a 1)) if  (!= ?b 0)
(< (< ?b 0) ?a) ==> 0 if (<= ?a 0)
(< (< ?b 0) ?a) <=> (< (< ?a ?b) ?a) if  (<= ?a 0)
(< (< ?b ?c) ?a) ==> (< (< ?b 0) ?a) if (<= ?a 0)
(< (< 0 ?b) ?a) <=> (< (< ?b 1) ?a) if  (<= ?a 0)
(< (< ?b 1) ?a) <=> (< (< ?b 0) ?a) if  (<= ?a 0)
?a <=> (- ?a) if  (== ?a 0)
(* ?a 0) ==> 0
(/ ?a 1) <=> ?a
(* ?a 0) <=> (* 0 ?a)
(* 0 ?a) <=> (/ 0 ?a)
(* 0 ?a) <=> (/ ?a 0)
(/ ?a 1) <=> (- ?a 0)
(/ ?a 1) <=> (* ?a 1)
(/ ?a 1) <=> (+ 0 ?a)
(/ ?a 1) <=> (* 1 ?a)
(/ ?a 1) <=> (+ ?a 0)
(- ?a ?a) <=> (* ?a 0)
(- (- ?a)) <=> (/ ?a 1)
(- ?a) <=> (- 0 ?a)
(* ?a ?b) <=> (* ?b ?a)
(/ ?a ?a) ==> 1 if (!= ?a 0)
(/ ?a ?a) ==> 1 if (< 0 ?a)
(/ ?a ?a) ==> 1 if (< ?a 0)
(- ?b ?a) ==> 0 if (== ?a ?b)
?a ==> 0 if (== ?a 0)
(* ?b ?a) ==> (* ?a ?a) if (== ?b ?a)
(* ?b ?a) ==> (* ?b ?b) if (== ?b ?a)
(/ ?a ?b) ==> (/ ?a ?a) if (== ?b ?a)
(/ ?a ?b) <=> (/ ?b ?a) if  (== ?b ?a)
(/ ?b ?a) ==> (/ ?a ?a) if (== ?a ?b)
(+ ?b ?a) <=> (- ?b ?a) if  (== ?a 0)
(/ 1 ?a) <=> (+ ?a ?a) if  (== ?a 0)
(* ?b ?a) ==> (/ 1 ?b) if (== ?b 0)
(/ ?b ?a) ==> (/ 1 ?a) if (== ?a 0)
(/ 1 ?a) <=> (* ?a ?a) if  (== ?a 0)
(/ ?b ?a) ==> (/ 1 ?b) if (== ?b 0)
(- 1 ?a) <=> (+ ?a 1) if  (== ?a 0)
(+ ?a (- ?a)) ==> 0
(- ?a (- ?b)) <=> (+ ?b ?a)
(- ?a (- ?a)) <=> (+ ?a ?a)
(/ ?b (- ?a)) <=> (- (/ ?b ?a))
(/ (- ?b) ?a) <=> (- (/ ?b ?a))
(+ ?b (- ?a)) <=> (- (- ?a ?b))
(- ?b (- ?a)) <=> (- ?a (- ?b))
(/ ?a (- ?a)) <=> (/ (- ?a) ?a)
(- (/ ?a ?a)) <=> (/ (- ?a) ?a)
(- (* ?b ?a)) <=> (* ?a (- ?b))
(- (- ?b) ?a) <=> (- (+ ?a ?b))
(- ?a (- 1)) <=> (+ ?a 1)
(- (- 1 ?a)) <=> (- ?a 1)
(- 1 (- ?a)) <=> (- ?a (- 1))
(- (/ 1 ?a)) <=> (/ (- 1) ?a)
(/ 1 (- ?a)) <=> (/ (- 1) ?a)
(/ ?a (- 1)) <=> (* ?a (- 1))
(+ (- ?a) 1) <=> (- (- ?a 1))
(+ ?a (- 1)) <=> (- (- 1 ?a))
(- (- 1) ?a) <=> (- (+ ?a 1))
(- (- ?a) 1) <=> (- (+ ?a 1))
(/ 1 (+ ?a ?a)) ==> 0
(* ?a (/ ?a ?a)) <=> ?a
(+ ?c (- ?b ?a)) <=> (- (+ ?b ?c) ?a)
(* ?b (+ ?a ?a)) <=> (* ?a (+ ?b ?b))
(+ ?b (- ?b ?a)) <=> (- (+ ?b ?b) ?a)
(/ ?c (* ?b ?a)) <=> (/ (/ ?c ?a) ?b)
(* ?c (* ?b ?a)) <=> (* ?b (* ?c ?a))
(- (- ?c ?b) ?a) <=> (- ?c (+ ?a ?b))
(/ (* ?a ?b) ?a) <=> (* ?b (/ ?a ?a))
(/ (* ?a ?b) ?a) <=> (/ ?b (/ ?a ?a))
(/ ?b (* ?b ?a)) <=> (/ (/ ?b ?a) ?b)
(/ ?a (* ?b ?a)) <=> (/ (/ ?a ?a) ?b)
(+ ?b (+ ?a ?a)) <=> (+ ?a (+ ?a ?b))
(* ?b (* ?a ?a)) <=> (* ?a (* ?a ?b))
(* ?b (- 1 ?a)) <=> (- ?b (* ?b ?a))
(* ?b (+ ?a 1)) <=> (+ ?b (* ?b ?a))
(* ?a (- 1 ?a)) <=> (- ?a (* ?a ?a))
(/ 1 (+ ?a ?a)) <=> (/ ?a (+ ?a ?a))
(* ?a (- ?b 1)) <=> (- (* ?b ?a) ?a)
(* ?b (/ 1 ?a)) <=> (/ ?b (/ 1 ?a))
(/ 1 (/ 1 ?a)) <=> (/ ?a (* ?a ?a))
(/ 1 (/ 1 ?a)) <=> (/ (/ ?a ?a) ?a)
(- ?b (+ ?a 1)) <=> (- (- ?b ?a) 1)
(- (+ ?b ?a) 1) <=> (- ?a (- 1 ?b))
(+ ?b (- ?a ?b)) ==> (- 1 (- 1 ?a))
(- 1 (- 1 ?a)) <=> (/ (* ?a ?a) ?a)
(- 1 (- 1 ?a)) <=> (* ?a (/ ?a ?a))
(- 1 (- 1 ?a)) <=> (/ ?a (/ ?a ?a))
(- (- ?a ?b) ?a) ==> (- (- 1 ?b) 1)
(- ?b (+ ?b ?a)) ==> (- (- 1 ?a) 1)
(/ 1 (* ?b ?a)) <=> (/ (/ 1 ?a) ?b)
(- 1 (+ ?b ?a)) <=> (- (- 1 ?b) ?a)
(- (- 1 ?b) ?a) <=> (- (- 1 ?a) ?b)
(/ (/ 1 ?a) ?a) <=> (/ ?a (/ 1 ?a))
(/ 1 (* ?a ?a)) <=> (/ ?a (/ 1 ?a))
(* ?a (/ 1 ?a)) <=> (/ ?a (/ 1 ?a))
(+ 1 (- 1 ?a)) <=> (- (+ 1 1) ?a)
(/ (- 1 ?a) ?a) ==> 0 if (<= 0 ?a)
(/ 1 (+ ?a 1)) ==> 0 if (< 0 ?a)
(/ 1 (* ?a ?a)) <=> (/ 1 ?a) if  (<= 0 ?a)
(/ ?a (+ ?a 1)) <=> (/ (- ?a 1) ?a) if  (<= 0 ?a)
(/ (- ?a 1) ?a) <=> (/ (- 1 ?a) ?a) if  (<= 0 ?a)
(/ ?a (- ?a 1)) ==> 0 if (<= ?a 0)
(* ?a (/ 1 ?a)) <=> (/ 1 ?a) if  (< 0 ?a)
(/ 1 (+ ?a 1)) <=> (/ (- 1 ?a) ?a) if  (< 0 ?a)
(/ 1 (+ ?a 1)) <=> (/ ?a (+ ?a 1)) if  (< 0 ?a)
(+ 1 (/ 1 ?a)) <=> (/ (+ ?a 1) ?a) if  (< 0 ?a)
(/ 1 (+ ?a 1)) <=> (/ (- ?a 1) ?a) if  (< 0 ?a)
(/ 1 (* ?a ?a)) <=> (- (/ 1 ?a)) if  (<= ?a 0)
(/ (+ ?a 1) ?a) <=> (/ ?a (- ?a 1)) if  (<= ?a 0)
(/ ?a (- 1 ?a)) <=> (/ ?a (- ?a 1)) if  (<= ?a 0)
(/ 1 (- ?a 1)) <=> (- (/ ?a ?a) 1) if  (<= ?a 0)
(* ?a (/ 1 ?a)) <=> (- (/ 1 ?a)) if  (< ?a 0)
(- 1 (/ 1 ?a)) <=> (/ (- ?a 1) ?a) if  (< ?a 0)
(/ 1 (- ?a 1)) <=> (/ (+ ?a 1) ?a) if  (< ?a 0)
(/ 1 (- 1 ?a)) <=> (/ ?a (- 1 ?a)) if  (< ?a 0)
(/ 1 (- ?a 1)) <=> (/ 1 (- 1 ?a)) if  (< ?a 0)
(min ?a ?a) <=> ?a
(max ?a ?a) <=> (min ?a ?a)
(min ?b ?a) <=> (min ?a ?b)
(max ?b ?a) <=> (max ?a ?b)
(min ?b ?a) ==> ?a if (<= ?a ?b)
(max ?b ?a) ==> ?b if (<= ?a ?b)
(min ?b ?a) ==> ?a if (< ?a ?b)
(max ?b ?a) ==> ?b if (< ?a ?b)
(min ?b ?a) ==> ?a if (== ?b ?a)
(max ?b ?a) ==> ?b if (== ?b ?a)
(min ?b ?a) <=> (max ?b ?a) if  (== ?b ?a)
(min ?b (max ?b ?a)) ==> ?b
(max ?a (min ?b ?a)) ==> ?a
(min ?c (min ?b ?a)) <=> (min ?a (min ?b ?c))
(min ?b (min ?b ?a)) <=> (min ?a (min ?b ?a))
(min ?a (max ?b ?a)) <=> (max ?a (min ?b ?a))
(max ?c (max ?b ?a)) <=> (max ?b (max ?c ?a))
(max ?c (min ?b ?a)) <=> (min ?a (max ?c ?b)) if  (<= ?c ?a)
(max ?c (min ?b ?a)) <=> (min ?a (max ?c ?b)) if  (< ?c ?a)
(max (min ?a ?c) (min ?b ?c)) <=> (min ?c (max ?b ?a))
(max ?b (min ?c (max ?b ?a))) <=> (max ?b (min ?a ?c))
(min ?a (max ?c (min ?b ?a))) <=> (max (min ?c ?a) (min ?b ?a))
(min (max ?b ?c) (max ?b ?a)) <=> (max ?b (min ?a (max ?b ?c)))
(max ?b (min ?c (max ?b ?a))) <=> (max ?b (min ?a (max ?b ?c)))
(min ?a 1) ==> 1 if (< 0 ?a)
(max ?a 1) <=> ?a if  (< 0 ?a)
(min ?a 1) <=> ?a if  (<= ?a 0)
(min 0 (min ?a 1)) <=> (min ?a 0)
(+ ?a (max 0 1)) <=> (+ ?a 1)
(+ ?a (max ?b 0)) <=> (max ?a (+ ?b ?a))
(+ ?a (min ?b 0)) <=> (min ?a (+ ?b ?a))
(max ?a (max 0 1)) <=> (max ?a 1)
(+ ?a (min 0 1)) <=> (min ?a (+ ?a 1))
(+ ?a (max 0 1)) <=> (max ?a (+ ?a 1))
(max 0 (min ?a 1)) <=> (min 1 (max ?a 0))
(+ 1 (min ?a 0)) <=> (min 1 (+ ?a 1))
(max 1 (+ ?a 1)) <=> (+ 1 (max ?a 0))
(min (+ ?a ?a) 1) <=> (min ?a 1) if  (<= 0 ?a)
(+ ?a (max ?a 1)) <=> (max (+ ?a ?a) 1) if  (<= 0 ?a)
(max ?b (+ ?a 1)) ==> ?b if (< ?a ?b)
(min ?b (+ ?a 1)) ==> (+ ?a 1) if (< ?a ?b)
(< (+ ?b (+ ?c ?a)) (min ?a (+ ?b ?a))) ==> (< (+ ?b (+ ?c ?c)) (min ?b ?c))
(< (+ ?b ?a) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?a) (+ ?a (min ?b ?c)))
(< (+ ?b ?a) (+ ?b (min ?a ?c))) ==> (< (+ ?b ?a) (min ?b (+ ?b ?a)))
(< (min ?b (+ ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?c) (+ ?b ?a))
(< (min ?b (+ ?a ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?b ?a))
(< (min ?b (+ ?b ?b)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a ?a))
(< (min ?d (+ ?c ?b)) (+ ?c (min ?b ?a))) <=> (< ?d (+ ?c (min ?b ?a)))
(< (min ?c (+ ?b ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?c ?b) (+ ?b (+ ?a ?a)))
(< (min ?a (+ ?a ?b)) (+ ?b (+ ?a ?a))) <=> (< (min ?a ?b) (+ ?b (+ ?a ?a)))
(< (+ ?b (+ ?c ?c)) (+ ?b (+ ?a ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?b ?a))
(< (+ ?b (min ?d ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?d) (min ?c (+ ?b ?a)))
(< (+ ?c (+ ?b ?b)) (min ?c (+ ?b ?a))) <=> (< (min ?c (+ ?b ?c)) (min ?c ?a))
(< (min ?b (+ ?b ?b)) (+ ?a (+ ?b ?b))) <=> (< (min ?b ?a) (+ ?b (+ ?a ?a)))
(< (+ ?c (min ?c ?b)) (+ ?b (min ?c ?a))) <=> (< (+ ?c ?c) (+ ?b (min ?b ?a)))
(< (+ ?b (+ ?a ?a)) (min ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (min ?b ?a))
(< (min ?b (+ ?a ?a)) (+ ?a (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a (+ ?a ?a)))
(< (min ?a (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?b ?a))
(< (+ ?b (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?b) (min ?c (+ ?a ?a)))
(< (+ ?b (+ ?a ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?a ?a)) (min ?b ?c))
(< (+ ?b (min ?b ?c)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?a ?a))
(< (+ ?b (+ ?d ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?d ?c)) (min ?b ?a))
(< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?a)) (+ ?a ?a))
(< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?a ?a))
(< (+ ?b (min ?d ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?d) (+ ?c (min ?b ?a)))
(< (+ ?b (min ?a ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?a) (+ ?c (min ?b ?a)))
(< (+ ?c (min ?d ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c ?d) (+ ?c (min ?b ?a)))
(< (min ?c (+ ?d ?b)) (min ?c (+ ?b ?a))) <=> (< (+ ?d ?b) (min ?c (+ ?b ?a)))
(< (min ?b (+ ?c ?b)) (min ?b (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?b (+ ?b ?a)))
(< (+ ?b (+ ?c ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?c ?c)) (min ?b ?a))
(< (+ ?b (min ?c ?b)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?b)) (+ ?a ?a))
(< (min ?c (min ?a ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?c ?a) (min ?b (+ ?a ?a)))
(< (min ?a (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?a (+ ?b ?a)))
(< (+ ?a (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?a) (min ?b (+ ?a ?a)))
(< (min ?b (+ ?c ?b)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?b) (min ?b (+ ?a ?a)))
(< (min ?c (+ ?d ?d)) (min ?c (+ ?b ?a))) <=> (< (+ ?d ?d) (min ?c (+ ?b ?a)))
(< (min ?b (+ ?b ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?b (+ ?b ?b)) (+ ?a (+ ?a ?a)))
(< (+ ?b (+ ?b ?b)) (+ ?a (+ ?a ?a))) <=> (< (min ?b (+ ?b ?a)) (min ?a (+ ?a ?a)))
(< (min ?c (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c (min ?c ?b)) (+ ?a (min ?b ?a)))
(< (+ ?b (+ ?c ?c)) (+ ?b (+ ?a ?a))) <=> (< (+ ?c (min ?c ?b)) (+ ?a (min ?b ?a)))
(< (min ?c (+ ?b ?a)) (+ ?b (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?b (min ?b ?a)))
(< (+ ?b (+ ?a ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (min ?a (+ ?b ?b)))
(< (+ ?c (+ ?b ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c (+ ?b ?b)) (min ?c (+ ?c ?a)))
(< (min ?b (+ ?b ?c)) (min ?b (+ ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (min ?b (+ ?b ?a)))
(< (min ?b (+ ?a ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?b)) (+ ?a (+ ?b ?b)))
(< (+ ?b (min ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b (+ ?b ?c)) (+ ?b (+ ?a ?a)))
(< (min ?b (+ ?b ?c)) (+ ?c (min ?b ?a))) <=> (< (min ?b (+ ?c ?a)) (+ ?c (min ?b ?a)))
(< (min ?c (+ ?b ?c)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (min ?c (+ ?b ?a)))
(< (+ ?b (min ?b ?a)) (min ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?a)) (min ?a (+ ?a ?a)))
(< (min ?b (+ ?b ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?a)) (min ?a (+ ?a ?a)))
(< (min ?b (+ ?b ?a)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?b (min ?b ?a)))
(< (min ?b (+ ?c ?d)) (min ?c (min ?b ?a))) <=> (< (min ?c (+ ?c ?d)) (min ?c (min ?b ?a)))
(< (+ ?a (+ ?b ?b)) (min ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (+ ?a (min ?a ?b)))
(< (+ ?a (min ?b ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?c (min ?b ?a)))
(< (min ?a (+ ?b ?b)) (+ ?b (min ?b ?a))) <=> (< (min ?a (+ ?b ?a)) (+ ?b (min ?b ?a)))
(< (+ ?b (min ?c ?a)) (min ?a (+ ?b ?a))) <=> (< (min ?a (+ ?b ?c)) (min ?a (+ ?b ?a)))
(< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?b)))
(< (min ?b (+ ?c ?c)) (min ?b (+ ?a ?a))) <=> (< (min ?b (+ ?c ?c)) (min ?b (+ ?c ?a)))
(< (+ ?c (min ?b ?c)) (+ ?b (min ?b ?a))) <=> (< (+ ?c (min ?b ?c)) (+ ?b (min ?c ?a)))
(< (min ?b (+ ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?a (min ?c ?a)) (min ?b (+ ?a ?a)))
(< (+ ?b (min ?c ?a)) (+ ?b (+ ?b ?a))) <=> (< (min ?a (+ ?b ?c)) (+ ?b (+ ?b ?a)))
(< (+ ?d (min ?b ?c)) (min ?b (min ?d ?a))) <=> (< (+ ?d (min ?b ?c)) (min ?b ?a)) if  (< ?b 0)
(< (min ?a (+ ?c ?c)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?c) (min ?b (+ ?c ?a))) if  (< ?c 0)
(< (min ?b (+ ?c ?c)) (+ ?b (min ?b ?a))) <=> (< (+ ?c ?c) (+ ?b (min ?c ?a))) if  (< ?c 0)
(< (+ ?b (min ?d ?c)) (min ?b (+ ?a ?a))) <=> (< (+ ?b (min ?d ?c)) (+ ?a ?a)) if  (< ?d 0)
(< (+ ?d (min ?b ?c)) (min ?d (+ ?b ?a))) <=> (< (+ ?d (min ?b ?c)) (+ ?b ?a)) if  (< ?b 0)
(< (min ?d (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (min ?d ?c) (min ?b (+ ?a ?a))) if  (< ?d 0)
(< (min ?d (+ ?b ?c)) (min ?c (+ ?b ?a))) <=> (< (min ?d (+ ?b ?c)) (+ ?b ?a)) if  (< ?b 0)
(< (+ ?c (min ?d ?c)) (min ?c (+ ?b ?a))) <=> (< (+ ?c (min ?d ?c)) (+ ?b ?a)) if  (< ?d 0)
(< (min ?d (+ ?b ?c)) (min ?b (min ?c ?a))) <=> (< (min ?d (+ ?b ?c)) (min ?b ?a)) if  (< ?b 0)
(< (min ?d (+ ?c ?c)) (min ?c (min ?b ?a))) <=> (< (min ?d (+ ?c ?c)) (min ?b ?a)) if  (< ?c 0)
(< (+ ?c (min ?b ?c)) (min ?c (+ ?b ?a))) <=> (< (+ ?c (min ?b ?c)) (+ ?b ?a)) if  (< ?b 0)
(< (min ?b (+ ?c ?d)) (+ ?c (min ?b ?a))) <=> (< (+ ?c ?d) (+ ?c (min ?b ?a))) if  (< ?c 0)
(< (min ?c (min ?b ?a)) (+ ?a (+ ?a ?a))) <=> (< (min ?c ?b) (+ ?a (+ ?a ?a))) if  (< ?c 0)
(< (min ?c (+ ?b ?d)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?d) (+ ?c (min ?b ?a))) if  (< ?b 0)
(< (min ?c (+ ?b ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?a ?a)) if  (< ?b 0)
(< (min ?d (+ ?c ?c)) (min ?c (min ?b ?a))) <=> (< (min ?d (+ ?c ?c)) (min ?b ?a)) if  (< ?d 0)
(< (+ ?c (min ?d ?b)) (min ?c (+ ?b ?a))) <=> (< (+ ?c (min ?d ?b)) (+ ?b ?a)) if  (< ?d 0)
(< (+ ?d (min ?c ?b)) (min ?b (+ ?a ?a))) <=> (< (+ ?d (min ?c ?b)) (+ ?a ?a)) if  (< ?d 0)
(< (+ ?c (min ?d ?b)) (min ?c (min ?b ?a))) <=> (< (+ ?c (min ?d ?b)) (min ?c ?a)) if  (< ?c 0)
(< (+ ?d (min ?d ?c)) (min ?d (min ?b ?a))) <=> (< (+ ?d (min ?d ?c)) (min ?b ?a)) if  (< ?d 0)
(< (+ ?c (min ?b ?a)) (min ?c (+ ?a ?a))) <=> (< (+ ?c (min ?b ?a)) (+ ?a ?a)) if  (< ?b 0)
(< (+ ?d (min ?c ?b)) (min ?c (min ?b ?a))) <=> (< (+ ?d (min ?c ?b)) (min ?b ?a)) if  (< ?d 0)
(< (min ?a (+ ?b ?c)) (+ ?a (min ?b ?a))) <=> (< (+ ?b ?c) (+ ?a (min ?b ?a))) if  (< ?b 0)
(< (+ ?c (+ ?d ?d)) (min ?c (+ ?b ?a))) <=> (< (+ ?c (+ ?d ?d)) (+ ?b ?a)) if  (< ?d 0)
(< (+ ?b (min ?c ?d)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (min ?c ?d)) (+ ?b ?a)) if  (< ?b 0)
(< (min ?b (+ ?c ?c)) (+ ?a (min ?b ?c))) <=> (< (min ?b (+ ?c ?c)) (+ ?a (min ?b ?a))) if  (< ?b 0)
(< (+ ?b (min ?c ?d)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (min ?c ?d)) (min ?d (+ ?b ?a))) if  (< ?b 0)
(< (+ ?d (min ?d ?c)) (min ?d (min ?b ?a))) <=> (< (+ ?d (min ?d ?c)) (min ?c (min ?b ?a))) if  (< ?d 0)
(< (+ ?c (min ?d ?b)) (min ?c (min ?d ?a))) <=> (< (+ ?c (min ?d ?b)) (min ?c (min ?b ?a))) if  (< ?c 0)
(< (min ?b (+ ?c ?c)) (+ ?a (min ?c ?b))) <=> (< (min ?b (+ ?c ?c)) (+ ?a (min ?b ?a))) if  (< ?c 0)
(< (+ ?d (min ?b ?c)) (min ?c (+ ?a ?a))) <=> (< (+ ?d (min ?b ?c)) (min ?b (+ ?a ?a))) if  (< ?d 0)
(< (+ ?c (min ?c ?b)) (min ?c (+ ?a ?a))) <=> (< (+ ?c (min ?b ?a)) (min ?b (+ ?a ?a))) if  (< ?c 0)
(< (+ ?c (min ?c ?b)) (min ?b (+ ?a ?a))) <=> (< (+ ?c (min ?b ?a)) (min ?b (+ ?a ?a))) if  (< ?c 0)
(< (+ ?b (min ?b ?a)) (+ ?a (+ ?a ?a))) <=> (< (min ?a (+ ?b ?b)) (+ ?a (+ ?a ?a))) if  (< ?b 0)
(< (+ ?a (min ?b ?c)) (min ?b (min ?c ?a))) <=> (< (+ ?b (+ ?c ?a)) (+ ?c (min ?b ?a))) if  (< ?b 0)
(< (+ ?b (min ?a ?b)) (+ ?a (+ ?a ?a))) <=> (< (min ?a (+ ?b ?b)) (+ ?a (+ ?a ?a))) if  (< ?a 0)
(< (+ ?b (+ ?c ?a)) (max ?a (+ ?b ?a))) ==> (< (+ ?b (+ ?c ?c)) (max ?b ?c))
(< (+ ?c ?b) (max ?a (+ ?c ?b))) <=> (< (+ ?c ?b) ?a)
(< (+ ?b (max ?c ?a)) (+ ?b ?a)) <=> (< (max ?b (max ?c ?a)) ?a)
(< (max ?b (+ ?b ?a)) (max ?a (+ ?a ?a))) <=> (< ?b (max ?b ?a))
(< (+ ?c (max ?c ?b)) (+ ?a (max ?b ?a))) <=> (< (+ ?c ?b) (+ ?b ?a))
(< (+ ?a (+ ?b ?b)) (max ?a (+ ?a ?a))) <=> (< (+ ?b ?b) (max ?b ?a))
(< (+ ?c (+ ?b ?b)) (max ?c (+ ?b ?a))) <=> (< (+ ?c ?b) (max ?c ?a))
(< (+ ?b (max ?a ?d)) (max ?c (+ ?b ?a))) <=> (< (+ ?b (max ?a ?d)) ?c)
(< (max ?c (+ ?b ?a)) (+ ?b (+ ?a ?a))) <=> (< (max ?c ?b) (+ ?b (+ ?a ?a)))
(< (max ?a (+ ?a ?b)) (+ ?b (+ ?a ?a))) <=> (< (max ?a ?b) (+ ?b (+ ?a ?a)))
(< (+ ?c (max ?c ?b)) (+ ?a (max ?b ?a))) <=> (< (+ ?c ?b) (+ ?b (max ?c ?a)))
(< (max ?b (+ ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (max ?b ?c) (max ?c (+ ?b ?a)))
(< (max ?b (+ ?a ?a)) (+ ?b (+ ?a ?a))) <=> (< (max ?b ?a) (max ?b (+ ?b ?a)))
(< (+ ?b (+ ?a ?a)) (max ?b (+ ?b ?a))) <=> (< (+ ?b ?a) (max ?b (+ ?b ?a)))
(< (+ ?b (max ?d ?c)) (+ ?b (max ?c ?a))) <=> (< (+ ?b (max ?d ?c)) (+ ?b ?a))
(< (max ?b (+ ?b ?b)) (+ ?a (+ ?b ?b))) <=> (< (max ?b ?a) (+ ?b (+ ?a ?a)))
(< (+ ?c (max ?c ?b)) (+ ?b (max ?b ?a))) <=> (< (+ ?c ?c) (+ ?b (max ?b ?a)))
(< (+ ?c (max ?c ?b)) (+ ?b (max ?b ?a))) <=> (< (+ ?c ?c) (+ ?b (max ?c ?a)))
(< (+ ?b (max ?b ?a)) (max ?b (+ ?a ?a))) <=> (< (+ ?b ?a) (max ?a (+ ?a ?a)))
(< (max ?a (+ ?a ?b)) (+ ?a (+ ?a ?a))) <=> (< (max ?a ?b) (max ?b (+ ?a ?a)))
(< (+ ?b (+ ?a ?a)) (max ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (max ?b ?a))
(< (max ?b (+ ?b ?b)) (+ ?b (+ ?a ?a))) <=> (< (max ?b ?a) (max ?a (+ ?a ?a)))
(< (+ ?c (max ?c ?a)) (max ?b (+ ?a ?a))) <=> (< (+ ?c ?c) (max ?b (+ ?c ?a)))
(< (+ ?c (max ?c ?a)) (max ?b (+ ?a ?a))) <=> (< (+ ?c ?c) (max ?b (+ ?a ?a)))
(< (+ ?b (+ ?a ?a)) (max ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?a ?a)) (max ?b ?c))
(< (max ?b (+ ?a ?a)) (+ ?a (+ ?a ?a))) <=> (< (max ?b ?a) (+ ?a (+ ?a ?a)))
(< (+ ?b (max ?d ?c)) (+ ?c (max ?b ?a))) <=> (< (+ ?b (max ?d ?c)) (+ ?c ?a))
(< (max ?d (+ ?b ?c)) (+ ?b (max ?c ?a))) <=> (< (max ?d (+ ?b ?c)) (+ ?b ?a))
(< (max ?c (+ ?d ?c)) (max ?c (+ ?b ?a))) <=> (< (max ?c (+ ?d ?c)) (+ ?b ?a))
(< (max ?b (+ ?d ?c)) (max ?b (+ ?b ?a))) <=> (< (max ?b (+ ?d ?c)) (+ ?b ?a))
(< (+ ?b (max ?c ?a)) (+ ?b (max ?b ?a))) <=> (< (+ ?b (max ?c ?a)) (+ ?b ?b))
(< (max ?b (+ ?d ?c)) (max ?c (max ?b ?a))) <=> (< (max ?b (+ ?d ?c)) (max ?c ?a))
(< (+ ?b (max ?c ?b)) (+ ?a (max ?b ?a))) <=> (< (+ ?b (max ?c ?b)) (+ ?a ?a))
(< (+ ?c (max ?b ?c)) (+ ?b (max ?c ?a))) <=> (< (+ ?c (max ?b ?c)) (+ ?b ?a))
(< (max ?b (max ?a ?c)) (max ?a (+ ?b ?a))) <=> (< (max ?b (max ?a ?c)) (+ ?b ?a))
(< (+ ?b (max ?a ?c)) (+ ?a (max ?b ?a))) <=> (< (+ ?b (max ?a ?c)) (+ ?a ?a))
(< (max ?b (+ ?d ?c)) (max ?b (+ ?a ?a))) <=> (< (max ?b (+ ?d ?c)) (+ ?a ?a))
(< (+ ?c (max ?b ?a)) (+ ?a (max ?c ?b))) <=> (< (+ ?c (max ?b ?a)) (+ ?b ?a))
(< (max ?b (+ ?c ?b)) (max ?b (+ ?a ?a))) <=> (< (max ?b (+ ?c ?b)) (+ ?a ?a))
(< (max ?a (+ ?c ?b)) (max ?a (+ ?b ?a))) <=> (< (max ?a (+ ?c ?b)) (+ ?b ?a))
(< (max ?d (+ ?c ?c)) (max ?d (+ ?b ?a))) <=> (< (max ?d (+ ?c ?c)) (+ ?b ?a))
(< (max ?b (+ ?b ?b)) (max ?a (+ ?b ?a))) <=> (< (max ?b (+ ?b ?b)) (max ?a (+ ?a ?a)))
(< (max ?b (+ ?b ?b)) (max ?a (+ ?a ?a))) <=> (< (max ?b (+ ?b ?a)) (max ?a (+ ?a ?a)))
(< (max ?c (+ ?c ?b)) (max ?a (+ ?b ?a))) <=> (< (+ ?c (max ?c ?b)) (+ ?a (max ?b ?a)))
(< (max ?c (max ?d ?b)) (max ?c (max ?b ?a))) <=> (< (max ?c (max ?d ?b)) (max ?c (max ?d ?a)))
(< (+ ?b (+ ?a ?a)) (max ?b (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (max ?a (+ ?b ?b)))
(< (+ ?c (+ ?b ?b)) (+ ?c (max ?b ?a))) <=> (< (+ ?c (+ ?b ?b)) (max ?c (+ ?c ?a)))
(< (max ?b (+ ?a ?a)) (+ ?b (+ ?a ?a))) <=> (< (max ?a (+ ?b ?b)) (+ ?a (+ ?b ?b)))
(< (+ ?c (max ?b ?d)) (+ ?c (max ?b ?a))) <=> (< (+ ?c (max ?b ?d)) (+ ?c (max ?d ?a)))
(< (max ?d (max ?c ?b)) (max ?b (+ ?a ?a))) <=> (< (max ?d (max ?c ?b)) (max ?c (+ ?a ?a)))
(< (+ ?b (max ?c ?a)) (+ ?a (max ?b ?a))) <=> (< (+ ?b (max ?b ?c)) (+ ?a (max ?b ?a)))
(< (+ ?a (+ ?b ?b)) (max ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (+ ?a (max ?a ?b)))
(< (+ ?b (max ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (max ?b (+ ?b ?c)) (+ ?b (+ ?a ?a)))
(< (max ?a (+ ?b ?b)) (max ?a (+ ?a ?a))) <=> (< (max ?b (+ ?b ?b)) (max ?b (+ ?b ?a)))
(< (max ?c (max ?d ?b)) (max ?c (+ ?b ?a))) <=> (< (max ?c (max ?d ?b)) (max ?b (+ ?b ?a)))
(< (max ?c (+ ?b ?b)) (+ ?a (max ?b ?a))) <=> (< (max ?c (+ ?b ?a)) (max ?c (+ ?a ?a)))
(< (max ?b (+ ?c ?c)) (max ?b (+ ?a ?a))) <=> (< (max ?b (+ ?c ?a)) (max ?b (+ ?a ?a)))
(< (max ?c (+ ?b ?d)) (max ?c (+ ?b ?a))) <=> (< (max ?c (+ ?b ?d)) (+ ?b (max ?d ?a)))
(< (max ?a (max ?c ?b)) (max ?b (+ ?a ?a))) <=> (< (max ?a (max ?c ?b)) (max ?a (+ ?a ?a)))
(< (+ ?b (max ?a ?c)) (+ ?b (max ?b ?a))) <=> (< (+ ?b (max ?a ?c)) (+ ?b (max ?b ?c)))
(< (+ ?b (max ?d ?a)) (max ?c (+ ?b ?a))) <=> (< (+ ?b (max ?d ?a)) (max ?c (+ ?b ?d)))
(< (+ ?b (max ?a ?c)) (max ?c (+ ?b ?a))) <=> (< (+ ?b (max ?a ?c)) (max ?c (+ ?b ?c)))
(< (+ ?b (max ?c ?a)) (max ?b (+ ?b ?a))) <=> (< (+ ?b (max ?c ?a)) (max ?b (+ ?b ?c)))
(< (max ?c (+ ?b ?a)) (+ ?b (max ?b ?a))) <=> (< (max ?c (+ ?b ?a)) (max ?c (+ ?b ?b)))
(< (max ?b (max ?a ?c)) (max ?c (+ ?b ?a))) <=> (< (max ?b (max ?a ?c)) (max ?a (+ ?b ?a)))
(< (max ?b (max ?a ?c)) (max ?b (+ ?b ?a))) <=> (< (max ?b (max ?a ?c)) (max ?a (+ ?b ?a)))
(< (+ ?b (max ?c ?a)) (+ ?b (+ ?b ?a))) <=> (< (max ?a (+ ?b ?c)) (+ ?b (+ ?b ?a)))
(< (+ ?b (max ?c ?a)) (+ ?c (max ?b ?a))) <=> (< (+ ?b (max ?c ?a)) (+ ?a (max ?b ?c)))
(< (max ?a (+ ?b ?c)) (+ ?c (max ?b ?a))) <=> (< (max ?a (+ ?b ?c)) (max ?a (+ ?c ?a)))
(< (+ ?c (max ?c ?d)) (max ?c (max ?b ?a))) <=> (< (+ ?c (max ?d ?b)) (max ?c (max ?b ?a))) if  (< ?c 0)
(< (+ ?b (max ?c ?a)) (max ?b (+ ?a ?a))) <=> (< (+ ?b (max ?b ?c)) (max ?b (+ ?a ?a))) if  (< ?b 0)
(< (+ ?c (+ ?b ?a)) (+ ?a (max ?b ?d))) ==> (< (+ ?c (+ ?c ?c)) (max ?c (max ?b ?a))) if (< ?c 0)
(< (+ ?b (+ ?a ?d)) (+ ?d (max ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b (+ ?a ?a))) if (< ?b 0)
(< (+ ?c (+ ?b ?a)) (+ ?c (max ?b ?a))) <=> (< (+ ?a (max ?c ?b)) (max ?c (max ?b ?a))) if  (< ?c 0)
(< (+ ?d (max ?c ?b)) (max ?c (max ?b ?a))) ==> (< (+ ?d (max ?c ?b)) (max ?d (max ?c ?b))) if (< ?d 0)
(< (+ ?b (max ?b ?c)) (max ?c (+ ?a ?a))) <=> (< (+ ?b (max ?b ?c)) (max ?c (+ ?b ?a))) if  (< ?b 0)
(< (+ ?b (max ?a ?c)) (max ?b (max ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b (+ ?a ?a))) if (< ?b 0)
(< (+ ?b (+ ?a ?c)) (+ ?a (max ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b (+ ?a ?a))) if (< ?b 0)
(< (+ ?d (+ ?c ?b)) (max ?a (+ ?c ?b))) <=> (< (+ ?c (+ ?d ?d)) (max ?c (max ?b ?a))) if  (< ?d 0)
(< (+ ?c (+ ?d ?d)) (max ?c (+ ?b ?a))) <=> (< (+ ?c (+ ?d ?d)) (max ?c (max ?b ?a))) if  (< ?d 0)
(< (+ ?c (+ ?d ?d)) (max ?c (max ?b ?a))) ==> (< (+ ?d (+ ?d ?d)) (max ?d (max ?c ?b))) if (< ?d 0)
(< (+ ?c (+ ?d ?d)) (max ?c (max ?b ?a))) ==> (< (+ ?c (+ ?d ?d)) (max ?d (+ ?c ?c))) if (< ?d 0)
(< (+ ?c (+ ?d ?d)) (max ?c (max ?b ?a))) ==> (< (+ ?d (+ ?d ?d)) (max ?d (+ ?c ?b))) if (< ?d 0)
(< (+ ?c (+ ?b ?a)) (max ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?c ?c)) (max ?b (+ ?a ?a))) if  (< ?c 0)
(== 1 1) <=> 1
(== 0 1) <=> 0
(== ?a ?a) ==> (== 1 1)
(== 0 0) <=> (== 1 1)
(== ?a (min ?b ?a)) <=> (== (min ?b ?a) ?a)
(== (min ?b ?a) 0) <=> (== 0 (min ?b ?a))
(== (min ?b ?a) 1) <=> (== 1 (min ?b ?a))
(== ?b ?a) ==> 0 if (!= ?b ?a)
(== 0 ?a) ==> 0 if (!= ?a 0)
(== (min ?c ?b) ?a) ==> 0 if (< ?b ?a)
(== ?c (min ?b ?a)) ==> 0 if (< ?a ?c)
(== ?b (min ?c ?a)) ==> (== ?b ?a) if (< ?a ?b)
(== (min ?c ?b) ?a) ==> (== ?b ?a) if (< ?a ?c)
(== ?c (min ?b ?a)) ==> (== ?c ?b) if (< ?c ?a)
(== 1 (min ?b ?a)) ==> 0 if (<= ?b 0)
(== 1 (min ?b ?a)) ==> (== 1 ?a) if (<= ?a 0)
(== (min ?c ?a) (min ?b ?a)) ==> (== ?a (min ?c ?a)) if (< ?c ?b)
(== 1 (min ?b ?a)) ==> 0 if (< ?b 0)
(== 1 (min ?b ?a)) ==> (== 0 ?a) if (< ?a 0)
(== 0 (min ?b ?a)) <=> (== 1 (min ?b ?a)) if  (< ?b 0)
(== ?a 1) <=> (== 1 ?a)
(== 0 ?a) <=> (== ?a 0)
(== ?a (max ?b ?a)) <=> (== (max ?b ?a) ?a)
(== 1 0) <=> (== 0 1)
(== (max ?b ?a) 0) <=> (== 0 (max ?b ?a))
(== (max ?b ?a) 1) <=> (== 1 (max ?b ?a))
(== ?b ?a) ==> 0 if (< ?b ?a)
(== ?b ?a) ==> 0 if (< ?a ?b)
(== 1 ?a) ==> 0 if (<= ?a 0)
(== ?c (max ?b ?a)) ==> 0 if (< ?c ?a)
(== (max ?c ?b) ?a) ==> 0 if (< ?a ?c)
(== ?b (max ?c ?a)) ==> (== ?b ?a) if (< ?b ?a)
(== (max ?c ?b) ?a) ==> (== ?b ?a) if (< ?c ?a)
(== ?b (max ?c ?a)) ==> (== ?b ?a) if (< ?c ?b)
(== 1 (max ?b ?a)) ==> (== 1 ?a) if (<= ?b 0)
(== (max ?c ?a) (max ?b ?a)) ==> (== ?a (max ?c ?a)) if (< ?b ?c)
(== 0 ?a) ==> 0 if (< ?a 0)
(== 0 (max ?b ?a)) ==> (== 0 ?a) if (< ?b 0)
(== 1 (max ?b ?a)) ==> (== 1 ?a) if (< ?b 0)
(== 1 ?a) <=> (== 0 ?a) if  (< ?a 0)
(max ?a (* ?a ?a)) <=> (* ?a ?a)
(min ?b (* ?a ?a)) ==> ?b if (<= ?b 0)
(max ?b (* ?a ?a)) ==> (* ?a ?a) if (<= ?b 0)
(min ?b (* ?a ?a)) ==> ?b if (< ?b 0)
(max ?b (* ?a ?a)) ==> (* ?a ?a) if (< ?b 0)
(* (min ?b ?a) (max ?b ?a)) <=> (* ?b ?a)
(min ?b (* ?a (max ?b ?a))) <=> (min ?b (* ?b (min ?b ?a)))
(min ?a (* ?b (* ?a ?a))) <=> (* ?b (* ?a ?a)) if  (< ?b 0)
(max ?b (max ?a (* ?b ?a))) <=> (max ?b (* ?b ?a)) if  (< ?a 0)
(min (* ?c ?b) (* ?c ?a)) <=> (* ?c (max ?b ?a)) if  (< ?c 0)
(min (* ?b ?a) (* ?a ?a)) <=> (* ?a (max ?b ?a)) if  (< ?a 0)
(max ?b (* ?a (max ?b ?a))) <=> (* ?a (max ?b ?a)) if  (< ?b 0)
(min ?b (* ?a (min ?a ?b))) <=> (min ?b (* ?a ?a)) if  (< ?a 0)
(max (* ?c ?b) (* ?b ?a)) <=> (* ?b (min ?c ?a)) if  (< ?b 0)
(max (* ?b ?a) (* ?a ?a)) <=> (* ?a (min ?b ?a)) if  (< ?a 0)
(min ?b (* ?b (min ?b ?a))) <=> (min ?b (* ?b ?a)) if  (< ?a 0)
(min ?a (* ?a (max ?b ?a))) <=> (min ?a (* ?b ?a)) if  (< ?a 0)
(max (* ?b ?a) (* ?a ?a)) <=> (max ?a (* ?a (min ?b ?a))) if  (< ?a 0)
(min ?a (* ?a (min ?b ?a))) ==> (max ?a (* ?a (* ?a ?a))) if (< ?a 0)
(min ?a (* ?b (max ?b ?a))) ==> (max ?a (* ?a (* ?a ?a))) if (< ?a 0)
(min ?b (* ?b (max ?b ?a))) <=> (max ?b (* ?a (* ?b ?b))) if  (< ?a 0)
(min ?a (max ?b (* ?b ?a))) <=> (min ?a (* ?a (min ?b ?a))) if  (< ?a 0)
(min ?c (* ?b (min ?b ?a))) <=> (min ?c (* ?a (max ?b ?a))) if  (< ?c 0)
(max ?b (* ?b (max ?b ?a))) <=> (max ?a (* ?b (max ?b ?a))) if  (< ?a 0)"#;

    let mut ruleset: Ruleset<Pred> = Default::default();
    for rule in rules.split("\n") {
        if !rule.trim().is_empty() {
            if let Ok((f, b)) = Rule::from_string(rule) {
                assert!(f.is_valid());
                ruleset.add(f);
                if let Some(b) = b {
                    assert!(b.is_valid());
                    ruleset.add(b);
                }
            } else {
                panic!("Failed to parse rule: {}", rule);
            }
        }
    }

    let against = r#"
(/ (max ?x ?y) ?z) ==> 0
"#;

    let mut against_set: Ruleset<Pred> = Default::default();
    for rule in against.split("\n") {
        if !rule.trim().is_empty() {
            if let Ok((f, b)) = Rule::from_string(rule) {
                assert!(!f.is_valid());
                against_set.add(f);
                if let Some(b) = b {
                    assert!(b.is_valid());
                    against_set.add(b);
                }
            } else {
                panic!("Failed to parse rule: {}", rule);
            }
        }
    }

    // let rws = base_implications.to_egg_rewrites();

    // for rule in against_set.iter() {
    //     assert!(ruleset.can_derive_cond(DeriveType::LhsAndRhs, rule, Limits::deriving(), &rws));
    // }

    // let mut egraph: EGraph<Pred, SynthAnalysis> = EGraph::default();
    // let l = egraph.add_expr(&Pred::instantiate(&"(/ (max ?x ?y) ?z)".parse().unwrap()));
    // let r = egraph.add_expr(&Pred::instantiate(
    //     &"(min (/ ?x ?z) (/ ?y ?z))".parse().unwrap(),
    // ));

    // let assumption: Assumption<Pred> = Assumption::new("(< z 0)".into()).unwrap();
    // assumption.insert_into_egraph(&mut egraph);
    // let assumption: Assumption<Pred> = Assumption::new("(!= z 0)".into()).unwrap();
    // assumption.insert_into_egraph(&mut egraph);

    // let runner = Runner::default()
    //     .with_egraph(egraph)
    //     .run(ruleset.iter().map(|r| r.rewrite).collect());
}
