use num::{rational::Ratio, BigInt, Signed, ToPrimitive, Zero};
use num_bigint::ToBigInt;
use ruler::{
    enumo::{Ruleset, Scheduler, Workload},
    *,
};
use std::{ops::*, time::Instant};
use z3::ast::Ast;

/// define `Constant` for rationals.
pub type Constant = Ratio<BigInt>;

fn mk_rat(n: i64, d: i64) -> Ratio<BigInt> {
    if d.is_zero() {
        panic!("mk_rat: denominator is zero!");
    }
    let n = n
        .to_bigint()
        .unwrap_or_else(|| panic!("could not make bigint from {}", n));
    let d = d
        .to_bigint()
        .unwrap_or_else(|| panic!("could not make bigint from {}", d));

    Ratio::new(n, d)
}

egg::define_language! {
  pub enum Math {
    "+" = Add([Id; 2]),
    "-" = Sub([Id; 2]),
    "*" = Mul([Id; 2]),
    "/" = Div([Id; 2]),
    "~" = Neg(Id),
    "fabs" = Abs(Id),
    Lit(Constant),
    Var(egg::Symbol),
  }
}

impl SynthLanguage for Math {
    type Constant = Constant;

    fn eval<'a, F>(&'a self, cvec_len: usize, mut get_cvec: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>,
    {
        match self {
            Math::Add([x, y]) => map!(get_cvec, x, y => Some(x + y)),
            Math::Sub([x, y]) => map!(get_cvec, x, y => Some(x - y)),
            Math::Mul([x, y]) => map!(get_cvec, x, y => Some(x * y)),
            Math::Div([x, y]) => map!(get_cvec, x, y => {
              if y.is_zero() {
                None
              } else {
                Some(x / y)
              }
            }),
            Math::Neg(x) => map!(get_cvec, x => Some(-x)),
            Math::Abs(a) => map!(get_cvec, a => Some(a.abs())),
            Math::Lit(c) => vec![Some(c.clone()); cvec_len],
            Math::Var(_) => vec![],
        }
    }

    fn mk_interval<'a, F>(&'a self, mut get_interval: F) -> Interval<Self::Constant>
    where
        F: FnMut(&'a Id) -> &'a Interval<Self::Constant>,
    {
        match self {
            Math::Lit(n) => Interval::new(Some(n.clone()), Some(n.clone())),
            Math::Var(_) => Interval::default(),
            Math::Neg(x) => neg(get_interval(x)),
            Math::Abs(a) => abs(get_interval(a)),
            Math::Add([x, y]) => add(get_interval(x), get_interval(y)),
            Math::Sub([x, y]) => add(get_interval(x), &neg(get_interval(y))),
            Math::Mul([x, y]) => mul(get_interval(x), get_interval(y)),
            Math::Div([x, y]) => mul(get_interval(x), &recip(get_interval(y))),
        }
    }

    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]) {
        let consts = vec![Some(mk_rat(-1, 1)), Some(mk_rat(0, 1)), Some(mk_rat(1, 1))];
        let cvecs = self_product(&consts, vars.len());

        egraph.analysis.cvec_len = cvecs[0].len();

        for (i, v) in vars.iter().enumerate() {
            let id = egraph.add(Math::Var(Symbol::from(v.clone())));
            let cvec = cvecs[i].clone();
            egraph[id].data.cvec = cvec;
        }
    }

    fn mk_var(sym: egg::Symbol) -> Self {
        Math::Var(sym)
    }

    fn to_var(&self) -> Option<Symbol> {
        match self {
            Math::Var(v) => Some(*v),
            _ => None,
        }
    }

    fn validate(lhs: &Pattern<Self>, rhs: &Pattern<Self>) -> ValidationResult {
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let lexpr = egg_to_z3(&ctx, Self::instantiate(lhs).as_ref());
        let rexpr = egg_to_z3(&ctx, Self::instantiate(rhs).as_ref());
        solver.assert(&lexpr._eq(&rexpr).not());
        match solver.check() {
            z3::SatResult::Unsat => ValidationResult::Valid,
            z3::SatResult::Unknown => ValidationResult::Unknown,
            z3::SatResult::Sat => ValidationResult::Invalid,
        }
    }

    fn is_constant(&self) -> bool {
        matches!(self, Math::Lit(_))
    }

    fn mk_constant(c: Self::Constant, _egraph: &mut EGraph<Self, SynthAnalysis>) -> Self {
        Math::Lit(c)
    }
}

impl Math {
    fn run_workload(workload: Workload, prior: Ruleset<Self>, limits: Limits) -> Ruleset<Self> {
        let t = Instant::now();

        let egraph = workload.to_egraph::<Self>();
        let compressed = Scheduler::Compress(limits).run(&egraph, &prior);

        let mut candidates = Ruleset::cvec_match(&compressed);

        let num_prior = prior.len();
        let chosen = candidates.minimize(prior, limits);
        let time = t.elapsed().as_secs_f64();

        println!(
            "Learned {} bidirectional rewrites ({} total rewrites) in {} using {} prior rewrites",
            chosen.bidir_len(),
            chosen.len(),
            time,
            num_prior
        );

        chosen.pretty_print();

        chosen
    }

    fn run_workload_fast_match(
        workload: Workload,
        prior: Ruleset<Self>,
        limits: Limits,
    ) -> Ruleset<Self> {
        let t = Instant::now();

        let egraph = workload.to_egraph::<Self>();
        let compressed = Scheduler::Compress(limits).run(&egraph, &prior);
        let mut candidates = Ruleset::fast_cvec_match(&compressed);

        let num_prior = prior.len();
        let chosen = candidates.minimize(prior, limits);
        let time = t.elapsed().as_secs_f64();

        println!(
            "Learned {} bidirectional rewrites ({} total rewrites) in {} using {} prior rewrites",
            chosen.bidir_len(),
            chosen.len(),
            time,
            num_prior
        );

        chosen.pretty_print();

        chosen
    }
}

fn egg_to_z3<'a>(ctx: &'a z3::Context, expr: &[Math]) -> z3::ast::Real<'a> {
    let mut buf: Vec<z3::ast::Real> = vec![];
    for node in expr.as_ref().iter() {
        match node {
            Math::Add([x, y]) => buf.push(z3::ast::Real::add(
                ctx,
                &[&buf[usize::from(*x)], &buf[usize::from(*y)]],
            )),
            Math::Sub([x, y]) => buf.push(z3::ast::Real::sub(
                ctx,
                &[&buf[usize::from(*x)], &buf[usize::from(*y)]],
            )),
            Math::Mul([x, y]) => buf.push(z3::ast::Real::mul(
                ctx,
                &[&buf[usize::from(*x)], &buf[usize::from(*y)]],
            )),
            Math::Div([x, y]) => {
                // Do NOT assume denominator is non-zero
                buf.push(z3::ast::Real::div(
                    &buf[usize::from(*x)],
                    &buf[usize::from(*y)],
                ))
            }
            Math::Neg(x) => buf.push(z3::ast::Real::unary_minus(&buf[usize::from(*x)])),
            Math::Abs(a) => {
                let inner = &buf[usize::from(*a)].clone();
                let zero = z3::ast::Real::from_real(ctx, 0, 1);
                buf.push(z3::ast::Bool::ite(
                    &z3::ast::Real::le(inner, &zero),
                    &z3::ast::Real::unary_minus(inner),
                    &inner,
                ));
            }
            Math::Lit(c) => buf.push(z3::ast::Real::from_real(
                ctx,
                (c.numer()).to_i32().unwrap(),
                (c.denom()).to_i32().unwrap(),
            )),
            Math::Var(v) => buf.push(z3::ast::Real::new_const(ctx, v.to_string())),
        }
    }
    buf.pop().unwrap()
}

// Interval helpers
#[derive(Debug, Clone, PartialEq, Eq)]
enum Sign {
    Positive,
    ContainsZero,
    Negative,
}

fn sign(interval: &Interval<Constant>) -> Sign {
    match (&interval.low, &interval.high) {
        (None, None) => Sign::ContainsZero,
        (Some(x), None) => {
            if x.is_positive() {
                Sign::Positive
            } else {
                Sign::ContainsZero
            }
        }
        (None, Some(y)) => {
            if y.is_negative() {
                Sign::Negative
            } else {
                Sign::ContainsZero
            }
        }
        (Some(x), Some(y)) => {
            if x.is_positive() && y.is_positive() {
                Sign::Positive
            } else if x.is_negative() && y.is_negative() {
                Sign::Negative
            } else {
                Sign::ContainsZero
            }
        }
    }
}

fn neg(interval: &Interval<Constant>) -> Interval<Constant> {
    let low = interval.low.clone();
    let high = interval.high.clone();
    Interval::new(high.map(|x| -x), low.map(|x| -x))
}

fn abs(interval: &Interval<Constant>) -> Interval<Constant> {
    let low = interval.low.clone();
    let high = interval.high.clone();

    match (low, high) {
        (None, None) => Interval::new(None, None),
        (Some(x), None) => {
            if x.is_negative() {
                Interval::new(Some(-x), None)
            } else {
                Interval::new(Some(x), None)
            }
        }
        (None, Some(y)) => {
            if y.is_negative() {
                Interval::new(None, Some(-y))
            } else {
                Interval::new(None, Some(y))
            }
        }
        (Some(x), Some(y)) => {
            if x.is_negative() {
                if y.is_negative() {
                    Interval::new(Some(-x), Some(-y))
                } else {
                    Interval::new(Some(-x), Some(y))
                }
            } else {
                if y.is_negative() {
                    Interval::new(Some(x), Some(-y))
                } else {
                    Interval::new(Some(x), Some(y))
                }
            }
        }
    }
}

fn add(a: &Interval<Constant>, b: &Interval<Constant>) -> Interval<Constant> {
    let add_opts = |x: Option<Constant>, y: Option<Constant>| x.zip(y).map(|(x, y)| x + y);
    let a = a.clone();
    let b = b.clone();
    Interval::new(add_opts(a.low, b.low), add_opts(a.high, b.high))
}

fn mul(a: &Interval<Constant>, b: &Interval<Constant>) -> Interval<Constant> {
    let mul_opts = |x: Option<Constant>, y: Option<Constant>| x.zip(y).map(|(x, y)| x * y);
    let (sign_a, sign_b) = (sign(a), sign(b));
    let a = a.clone();
    let b = b.clone();
    match (sign_a, sign_b) {
        (Sign::Negative, Sign::Negative) => {
            Interval::new(mul_opts(a.high, b.high), mul_opts(a.low, b.low))
        }
        (Sign::Positive, Sign::Positive) => {
            Interval::new(mul_opts(a.low, b.low), mul_opts(a.high, b.high))
        }
        (Sign::Positive, Sign::Negative) => {
            Interval::new(mul_opts(a.high, b.low), mul_opts(a.low, b.high))
        }
        (Sign::Negative, Sign::Positive) => {
            Interval::new(mul_opts(a.low, b.high), mul_opts(a.high, b.low))
        }

        (Sign::Positive, Sign::ContainsZero) => {
            Interval::new(mul_opts(a.high.clone(), b.low), mul_opts(a.high, b.high))
        }
        (Sign::ContainsZero, Sign::Positive) => {
            Interval::new(mul_opts(a.low, b.high.clone()), mul_opts(a.high, b.high))
        }

        (Sign::Negative, Sign::ContainsZero) => {
            Interval::new(mul_opts(a.low.clone(), b.high), mul_opts(a.low, b.low))
        }
        (Sign::ContainsZero, Sign::Negative) => {
            Interval::new(mul_opts(a.high, b.low.clone()), mul_opts(a.low, b.low))
        }

        (Sign::ContainsZero, Sign::ContainsZero) => {
            let al_bh = mul_opts(a.low.clone(), b.high.clone());
            let ah_bl = mul_opts(a.high.clone(), b.low.clone());
            let min = al_bh.zip(ah_bl).map(|(x, y)| x.min(y));

            let ah_bh = mul_opts(a.high, b.high);
            let al_bl = mul_opts(a.low, b.low);
            let max = ah_bh.zip(al_bl).map(|(x, y)| x.max(y));
            Interval::new(min, max)
        }
    }
}

fn recip(interval: &Interval<Constant>) -> Interval<Constant> {
    let interval = interval.clone();
    let sign = sign(&interval);
    match (interval.low, interval.high) {
        (Some(x), Some(y)) => match sign {
            Sign::ContainsZero => Interval::default(),
            _ => Interval::new(Some(y.recip()), Some(x.recip())),
        },
        _ => Interval::default(),
    }
}

#[cfg(test)]
pub mod test {
    use std::time::Duration;

    use super::*;
    use ruler::enumo::{Filter, Ruleset, Workload};

    fn interval(low: Option<i32>, high: Option<i32>) -> Interval<Constant> {
        let i32_to_constant = |x: i32| Ratio::new(x.to_bigint().unwrap(), 1.to_bigint().unwrap());
        Interval::new(low.map(i32_to_constant), high.map(i32_to_constant))
    }

    #[test]
    fn sign_test() {
        assert_eq!(sign(&interval(None, None)), Sign::ContainsZero);
        assert_eq!(sign(&interval(None, Some(-100))), Sign::Negative);
        assert_eq!(sign(&interval(None, Some(100))), Sign::ContainsZero);
        assert_eq!(sign(&interval(Some(-100), None)), Sign::ContainsZero);
        assert_eq!(sign(&interval(Some(100), None)), Sign::Positive);
        assert_eq!(sign(&interval(Some(-100), Some(-50))), Sign::Negative);
        assert_eq!(sign(&interval(Some(50), Some(100))), Sign::Positive);
        assert_eq!(sign(&interval(Some(-10), Some(100))), Sign::ContainsZero);
    }

    #[test]
    fn neg_interval_test() {
        assert_eq!(neg(&interval(None, None)), interval(None, None));
        assert_eq!(neg(&interval(Some(10), None)), interval(None, Some(-10)));
        assert_eq!(neg(&interval(Some(-10), None)), interval(None, Some(10)));
        assert_eq!(neg(&interval(None, Some(10))), interval(Some(-10), None));
        assert_eq!(neg(&interval(None, Some(-10))), interval(Some(10), None));
        assert_eq!(
            neg(&interval(Some(5), Some(10))),
            interval(Some(-10), Some(-5))
        );
    }

    #[test]
    fn add_interval_test() {
        assert_eq!(
            add(&interval(None, None), &interval(None, None)),
            interval(None, None)
        );
        assert_eq!(
            add(&interval(None, None), &interval(Some(-10), Some(10))),
            interval(None, None)
        );
        assert_eq!(
            add(&interval(Some(-10), Some(10)), &interval(None, None)),
            interval(None, None)
        );
        assert_eq!(
            add(
                &interval(Some(-20), Some(5)),
                &interval(Some(-10), Some(10))
            ),
            interval(Some(-30), Some(15))
        );
    }

    #[test]
    fn mul_interval_test() {
        assert_eq!(
            mul(&interval(None, Some(-3)), &interval(None, Some(-4))),
            interval(Some(12), None)
        );
        assert_eq!(
            mul(
                &interval(Some(-100), Some(-2)),
                &interval(Some(-50), Some(-20))
            ),
            interval(Some(40), Some(5000))
        );
        assert_eq!(
            mul(&interval(Some(2), None), &interval(Some(50), None)),
            interval(Some(100), None)
        );
        assert_eq!(
            mul(&interval(Some(30), Some(50)), &interval(Some(2), Some(3))),
            interval(Some(60), Some(150))
        );
        assert_eq!(
            mul(
                &interval(Some(-10), Some(-5)),
                &interval(Some(6), Some(100))
            ),
            interval(Some(-1000), Some(-30))
        );
        assert_eq!(
            mul(&interval(Some(3), Some(10)), &interval(None, Some(-1))),
            interval(None, Some(-3))
        );
        assert_eq!(
            mul(&interval(Some(2), Some(5)), &interval(Some(-3), Some(4))),
            interval(Some(-15), Some(20))
        );
        assert_eq!(
            mul(&interval(Some(-2), None), &interval(Some(3), Some(4))),
            interval(Some(-8), None)
        );
        assert_eq!(
            mul(&interval(None, None), &interval(Some(-10), Some(-4))),
            interval(None, None)
        );
        assert_eq!(
            mul(&interval(Some(-8), Some(6)), &interval(Some(-3), Some(-2))),
            interval(Some(-18), Some(24))
        );
        assert_eq!(
            mul(&interval(Some(-4), Some(6)), &interval(Some(-8), Some(10))),
            interval(Some(-48), Some(60))
        );
        assert_eq!(
            mul(
                &interval(Some(-100), Some(50)),
                &interval(Some(-5), Some(7))
            ),
            interval(Some(-700), Some(500))
        );
        assert_eq!(
            mul(&interval(Some(-5), Some(6)), &interval(Some(-4), Some(8))),
            interval(Some(-40), Some(48))
        );
        assert_eq!(
            mul(&interval(Some(-4), Some(10)), &interval(Some(-8), Some(6))),
            interval(Some(-80), Some(60))
        );
        assert_eq!(
            mul(&interval(None, Some(10)), &interval(Some(-5), Some(15))),
            interval(None, None)
        );
        assert_eq!(
            mul(&interval(Some(-4), Some(10)), &interval(Some(-8), None)),
            interval(None, None)
        );
    }

    #[test]
    fn recip_interval_test() {
        assert_eq!(recip(&interval(None, None)), interval(None, None));
        assert_eq!(
            recip(&interval(Some(50), Some(100))),
            Interval::new(
                Some(Ratio::new(1.to_bigint().unwrap(), 100.to_bigint().unwrap())),
                Some(Ratio::new(1.to_bigint().unwrap(), 50.to_bigint().unwrap())),
            )
        );
        assert_eq!(
            recip(&interval(Some(-10), Some(-5))),
            Interval::new(
                Some(Ratio::new(
                    1.to_bigint().unwrap(),
                    (-5).to_bigint().unwrap()
                )),
                Some(Ratio::new(
                    1.to_bigint().unwrap(),
                    (-10).to_bigint().unwrap()
                )),
            )
        );
    }

    fn replicate_ruler1_recipe() -> Ruleset<Math> {
        let mut rules = Ruleset::default();
        let limits = Limits::default();

        // Domain
        let lang = Workload::new(&["var", "const", "(uop expr)", "(bop expr expr)"]);
        let vars = &Workload::new(["a", "b", "c"]);
        let consts = &Workload::new(["0", "-1", "1"]);
        let uops = &Workload::new(["~", "fabs"]);
        let bops = &Workload::new(["+", "-", "*", "/"]);

        // Layer 1 (one op)
        println!("layer1");
        let layer1 = lang
            .clone()
            .iter_metric("expr", enumo::Metric::Depth, 2)
            .filter(Filter::Contains("var".parse().unwrap()))
            .plug_lang(vars, consts, uops, bops);
        let layer1_rules = Math::run_workload(layer1.clone(), rules.clone(), limits);
        rules.extend(layer1_rules);

        // Layer 2 (two ops)
        println!("layer2");
        let layer2 = lang
            .clone()
            .iter_metric("expr", enumo::Metric::Depth, 3)
            .filter(Filter::Contains("var".parse().unwrap()))
            .plug_lang(vars, consts, uops, bops);
        layer2.to_file("replicate_layer2_terms");
        let layer2_rules = Math::run_workload_fast_match(layer2.clone(), rules.clone(), limits);
        rules.extend(layer2_rules);

        rules
    }

    pub fn best_enumo_recipe() -> Ruleset<Math> {
        let mut rules = replicate_ruler1_recipe();
        let limits = Limits::default();

        // Contains var filter
        let contains_var_filter = Filter::Or(vec![
            Filter::Contains("a".parse().unwrap()),
            Filter::Contains("b".parse().unwrap()),
            Filter::Contains("c".parse().unwrap()),
        ]);

        // Safe filter
        let safe_filter = Filter::Invert(Box::new(Filter::Contains("(/ ?x 0)".parse().unwrap())));

        // Contains abs filter
        let contains_abs_filter = Filter::Contains("fabs".parse().unwrap());

        let vars = Workload::new(["a", "b", "c"]);
        let consts = Workload::new(["-1", "0", "1", "2"]);

        // Div
        println!("div");
        let div = Workload::new(["(/ v (/ v v))"]).plug("v", &vars);
        let div_rules = Math::run_workload(div, rules.clone(), limits);
        rules.extend(div_rules);

        // Nested fabs
        println!("nested fabs");
        let op_layer = Workload::new(["(uop expr)", "(bop expr expr)"])
            .plug("uop", &Workload::new(&["~", "fabs"]))
            .plug("bop", &Workload::new(&["+", "-", "*", "/"]));
        let layer1 = op_layer.clone().plug("expr", &vars.append(consts));
        let layer2 = op_layer
            .plug("expr", &layer1)
            .filter(safe_filter.clone())
            .filter(contains_var_filter.clone())
            .filter(contains_abs_filter);
        let nested_abs = Workload::new(["(fabs e)"]).plug("e", &layer2);
        let nested_abs_rules = Math::run_workload_fast_match(nested_abs, rules.clone(), limits);
        rules.extend(nested_abs_rules);

        rules
    }

    fn test_against_herbie(rules: &Ruleset<Math>, name: &str, duration: Duration) {
        let herbie: Ruleset<Math> = Ruleset::from_file("baseline/herbie-rational.rules");

        println!("Comparing rational to herbie...");
        rules.write_baseline_row(
            herbie,
            name,
            "herbie_baseline",
            "herbie.json",
            Limits {
                iter: 2,
                node: 150000,
            },
            duration,
        );
    }

    // #[test]
    fn run_all() {
        let start = Instant::now();
        let rules = replicate_ruler1_recipe();
        let duration = start.elapsed();

        rules.write_json_rules("rational_replicate.json");
        test_against_ruler1(&rules, "rational_replicate", duration);
        test_against_herbie(&rules, "herbie_rational_replicate", duration);

        let start = Instant::now();
        let rules = best_enumo_recipe();
        let duration = start.elapsed();

        rules.write_json_rules("rational_best.json");
        test_against_ruler1(&rules, "rational_best", duration);
        test_against_herbie(&rules, "herbie_rational_best", duration);
    }

    fn test_against_ruler1(rules: &Ruleset<Math>, name: &str, duration: Duration) {
        let ruler1: Ruleset<Math> = Ruleset::from_file("baseline/rational.rules");

        println!("Comparing rational to ruler1...");
        rules.write_baseline_row(
            ruler1,
            name,
            "oopsla",
            "baseline.json",
            Limits {
                iter: 2,
                node: 150000,
            },
            duration,
        );
    }
}
