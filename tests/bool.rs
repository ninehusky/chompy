use ruler::*;
use std::ops::*;

egg::define_language! {
  pub enum Bool {
    "~" = Not(Id),
    "&" = And([Id; 2]),
    "|" = Or([Id; 2]),
    "^" = Xor([Id; 2]),
    "->" = Implies([Id; 2]),
    Lit(bool),
    Var(egg::Symbol),
  }
}

impl SynthLanguage for Bool {
    type Constant = bool;

    fn eval<'a, F>(&'a self, cvec_len: usize, mut get_cvec: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>,
    {
        match self {
            Bool::Not(x) => map!(get_cvec, x => Some(x.not())),
            Bool::And([x, y]) => map!(get_cvec, x, y => Some(*x & *y)),
            Bool::Or([x, y]) => map!(get_cvec, x, y => Some(*x | *y)),
            Bool::Xor([x, y]) => map!(get_cvec, x, y => Some(*x ^ *y)),
            Bool::Implies([x, y]) => map!(get_cvec, x, y => Some(!(*x) | *y)),
            Bool::Lit(c) => vec![Some(*c); cvec_len],
            Bool::Var(_) => vec![],
        }
    }

    fn mk_interval<'a, F>(&'a self, mut get_interval: F) -> Interval<Self::Constant>
    where
        F: FnMut(&'a Id) -> &'a Interval<Self::Constant>,
    {
        let unwrap_interval = |interval: &Interval<Self::Constant>| {
            (
                interval
                    .low
                    .expect("Bool shouldn't have infinite intervals"),
                interval
                    .high
                    .expect("Bool shouldn't have infinite intervals"),
            )
        };
        match self {
            Bool::Lit(c) => Interval::new(Some(*c), Some(*c)),
            Bool::Var(_) => Interval::new(Some(false), Some(true)),
            Bool::Not(x) => {
                let (low, high) = unwrap_interval(get_interval(x));
                Interval::new(Some(!high), Some(!low))
            }
            Bool::And([x, y]) => {
                let (x_low, x_high) = unwrap_interval(get_interval(x));
                let (y_low, y_high) = unwrap_interval(get_interval(y));
                Interval::new(Some(x_low && y_low), Some(x_high && y_high))
            }
            Bool::Or([x, y]) => {
                let (x_low, x_high) = unwrap_interval(get_interval(x));
                let (y_low, y_high) = unwrap_interval(get_interval(y));
                Interval::new(Some(x_low || y_low), Some(x_high || y_high))
            }
            Bool::Xor([x, y]) => {
                let (x_low, x_high) = unwrap_interval(get_interval(x));
                let (y_low, y_high) = unwrap_interval(get_interval(y));
                if x_low == x_high && y_low == y_high {
                    Interval::new(Some(x_low != y_low), Some(x_low != y_low))
                } else {
                    Interval::new(Some(false), Some(true))
                }
            }
            Bool::Implies([x, y]) => {
                let (x_low, x_high) = unwrap_interval(get_interval(x));
                let (y_low, y_high) = unwrap_interval(get_interval(y));
                Interval::new(Some(!x_high || y_low), Some(!x_low || y_high))
            }
        }
    }

    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]) {
        println!("initializing vars: {:?}", vars);

        let consts = vec![Some(true), Some(false)];
        let cvecs = self_product(&consts, vars.len());

        egraph.analysis.cvec_len = cvecs[0].len();

        for (i, v) in vars.iter().enumerate() {
            let id = egraph.add(Bool::Var(Symbol::from(v.clone())));
            let cvec = cvecs[i].clone();
            egraph[id].data.cvec = cvec;
        }
    }

    fn mk_var(sym: egg::Symbol) -> Self {
        Bool::Var(sym)
    }

    fn to_var(&self) -> Option<Symbol> {
        match self {
            Bool::Var(v) => Some(*v),
            _ => None,
        }
    }

    fn validate(_lhs: &Pattern<Self>, _rhs: &Pattern<Self>) -> ValidationResult {
        ValidationResult::Valid
    }

    fn is_constant(&self) -> bool {
        matches!(self, Bool::Lit(_))
    }

    fn mk_constant(c: Self::Constant, _egraph: &mut EGraph<Self, SynthAnalysis>) -> Self {
        Bool::Lit(c)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ruler::enumo::{Ruleset, Workload};
    use serde_json::*;
    use std::fs::OpenOptions;
    use std::io::Write;
    use std::time::Instant;

    fn iter_bool(n: usize) -> Workload {
        Workload::iter_lang(
            n,
            &["true", "false"],
            &["a", "b", "c"],
            &["~"],
            &["&", "|", "^", "->"],
        )
    }

    #[test]
    fn dsl() {
        let mut all_rules: Ruleset<Bool> = Ruleset::default();
        let atoms3 = iter_bool(3);
        assert_eq!(atoms3.force().len(), 93);

        let egraph = all_rules.compress_workload(atoms3, Limits::default());
        let mut candidates = Ruleset::cvec_match(&egraph);
        let rules3 = candidates.minimize(all_rules.clone(), Limits::default());
        assert_eq!(rules3.len(), 14);
        all_rules.extend(rules3);

        let atoms4 = iter_bool(4);
        assert_eq!(atoms4.force().len(), 348);

        let egraph = all_rules.compress_workload(atoms4, Limits::default());
        candidates = Ruleset::cvec_match(&egraph);
        let rules4 = candidates.minimize(all_rules.clone(), Limits::default());
        assert_eq!(rules4.len(), 3);
        all_rules.extend(rules4);

        let atoms5 = iter_bool(5);
        assert_eq!(atoms5.force().len(), 4599);

        let egraph = all_rules.compress_workload(atoms5, Limits::default());
        candidates = Ruleset::cvec_match(&egraph);
        let rules5 = candidates.minimize(all_rules.clone(), Limits::default());
        assert_eq!(rules5.len(), 15);
        all_rules.extend(rules5);

        assert_eq!(all_rules.len(), 32);
    }

    #[test]
    fn simple() {
        let mut all_rules = Ruleset::default();
        let atoms3 = iter_bool(3);
        assert_eq!(atoms3.force().len(), 93);

        let rules3 = Bool::run_workload(atoms3, all_rules.clone(), Limits::default());
        assert_eq!(rules3.len(), 14);
        all_rules.extend(rules3);

        let atoms4 = iter_bool(4);
        assert_eq!(atoms4.force().len(), 348);

        let rules4 = Bool::run_workload(atoms4, all_rules.clone(), Limits::default());
        assert_eq!(rules4.len(), 3);
        all_rules.extend(rules4);

        let atoms5 = iter_bool(5);
        assert_eq!(atoms5.force().len(), 4599);

        let rules5 = Bool::run_workload(atoms5, all_rules.clone(), Limits::default());
        assert_eq!(rules5.len(), 15);
        all_rules.extend(rules5);

        assert_eq!(all_rules.len(), 32);
    }

    #[test]
    fn bool_oopsla_equiv() {
        let mut all_rules = Ruleset::default();
        let start = Instant::now();

        let layer_1 = Workload::make_layer(1, &[], &["ba", "bb", "bc"], &["~"], &["&", "|", "^"]);
        let rules_1 = Bool::run_workload(layer_1, all_rules.clone(), Limits::default());
        all_rules.extend(rules_1);

        let layer_2 = Workload::make_layer(2, &[], &["ba", "bb", "bc"], &["~"], &["&", "|", "^"]);
        let rules_2 = Bool::run_workload(layer_2, all_rules.clone(), Limits::default());
        all_rules.extend(rules_2);

        let layer_3 = Workload::make_layer(3, &[], &["ba", "bb", "bc"], &["~"], &["&", "|", "^"]);
        let rules_3 = Bool::run_workload(layer_3, all_rules.clone(), Limits::default());
        all_rules.extend(rules_3);

        let duration = start.elapsed();
        all_rules.to_file("equivalent/bool.rules");

        let baseline = Ruleset::<_>::from_file("baseline/bool.rules");
        let (can, cannot) = all_rules.derive(
            baseline.clone(),
            Limits {
                iter: 3,
                node: 1000000,
            },
        );

        let (canr, cannotr) = baseline.derive(
            all_rules.clone(),
            Limits {
                iter: 3,
                node: 1000000,
            },
        );

        let rules = json!({
            "rules": all_rules.to_str_vec(),
        });

        let rules_str = rules.to_string();

        let mut rules_file = OpenOptions::new()
            .write(true)
            .open("rep/json/rules/bool.json")
            .expect("Unable to open file");
        rules_file
            .write_all(rules_str.as_bytes())
            .expect("write failed");

        let derivability = json!({
            "forwards derivable": can.to_str_vec(),
            "forwards underivable": cannot.to_str_vec(),
            "backwards derivable": canr.to_str_vec(),
            "backwards underivable": cannotr.to_str_vec()
        });

        let derivability_str = derivability.to_string();

        let mut derivability_file = OpenOptions::new()
            .write(true)
            .open("rep/json/derivable_rules/bool.json")
            .expect("Unable to open file");
        derivability_file
            .write_all(derivability_str.as_bytes())
            .expect("write failed");

        let num_rules = &all_rules.len();
        let forwards_derivable = &can.len();
        let backwards_derivable = &canr.len();
        let time = &duration.as_secs();

        let stats = json!({
            "spec": "bool",
            "num_rules": num_rules,
            "num_baseline": 51,
            "enumo_derives_oopsla": forwards_derivable,
            "oopsla_derives_enumo": backwards_derivable,
            "time": time
        });

        let stats_str = stats.to_string();

        let mut file = OpenOptions::new()
            .append(true)
            .open("rep/json/output.json")
            .expect("Unable to open file");
        file.write_all(stats_str.as_bytes()).expect("write failed");
        file.write_all(", ".as_bytes()).expect("write failed");
    }

    #[test]
    fn round_trip_to_file() {
        let rules: Ruleset<Bool> = Ruleset::from_str_vec(&[
            "(^ ?b ?a) ==> (^ ?a ?b)",
            "(& ?b ?a) ==> (& ?a ?b)",
            "(| ?b ?a) ==> (| ?a ?b)",
            "(& ?a ?a) ==> ?a",
            "?a ==> (~ (~ ?a))",
        ]);

        rules.to_file("out.txt");

        let read: Ruleset<Bool> = Ruleset::from_file("out.txt");

        assert_eq!(rules, read)
    }

    #[test]
    fn derive_rules() {
        let three = Bool::run_workload(
            iter_bool(3),
            Ruleset::default(),
            Limits {
                iter: 4,
                node: 1000000,
            },
        );
        three.to_file("three.txt");

        let four = Bool::run_workload(
            iter_bool(4),
            Ruleset::default(),
            Limits {
                iter: 4,
                node: 1000000,
            },
        );
        four.to_file("four.txt");

        let (can, cannot) = three.derive(
            four,
            Limits {
                iter: 10,
                node: 1000000,
            },
        );
        assert_eq!(can.len(), 10);
        assert_eq!(cannot.len(), 6);
    }
}
